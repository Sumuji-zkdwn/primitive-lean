package com.primitive.neonorbit;

import android.app.Activity;
import android.content.Context;
import android.content.SharedPreferences;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.LinearGradient;
import android.graphics.Paint;
import android.graphics.Path;
import android.graphics.RectF;
import android.graphics.Shader;
import android.graphics.Typeface;
import android.media.AudioManager;
import android.media.ToneGenerator;
import android.os.Bundle;
import android.view.HapticFeedbackConstants;
import android.view.MotionEvent;
import android.view.View;
import android.view.WindowManager;

import java.util.ArrayList;
import java.util.Locale;
import java.util.Random;

/** NEON ORBIT: a one-finger, offline gravity arcade game. */
public final class MainActivity extends Activity {
    private GameSurface surface;
    private ToneGenerator tones;

    @Override public void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        getWindow().addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON);
        getWindow().getDecorView().setSystemUiVisibility(
            View.SYSTEM_UI_FLAG_FULLSCREEN | View.SYSTEM_UI_FLAG_HIDE_NAVIGATION |
            View.SYSTEM_UI_FLAG_IMMERSIVE_STICKY | View.SYSTEM_UI_FLAG_LAYOUT_STABLE |
            View.SYSTEM_UI_FLAG_LAYOUT_FULLSCREEN | View.SYSTEM_UI_FLAG_LAYOUT_HIDE_NAVIGATION);
        try { tones = new ToneGenerator(AudioManager.STREAM_MUSIC, 42); }
        catch (RuntimeException ignored) { tones = null; }
        surface = new GameSurface(this);
        setContentView(surface);
    }

    @Override protected void onPause() {
        super.onPause();
        if (surface != null) surface.hostPause();
    }
    @Override protected void onResume() {
        super.onResume();
        if (surface != null) surface.hostResume();
    }
    @Override protected void onDestroy() {
        if (tones != null) { tones.release(); tones = null; }
        super.onDestroy();
    }

    private final class GameSurface extends View {
        private static final int READY = 0, PLAY = 1, PAUSE = 2, FINISH = 3;
        private static final int GOLD = 0, CLOCK = 1, FEVER = 2;
        private final int DARK = Color.rgb(5, 9, 24);
        private final int BLUE = Color.rgb(88, 236, 255);
        private final int GOLDEN = Color.rgb(255, 210, 101);
        private final int PINK = Color.rgb(255, 72, 152);
        private final int RED = Color.rgb(255, 83, 106);
        private final int LIME = Color.rgb(142, 252, 181);
        private final int WHITE = Color.rgb(239, 245, 255);
        private final int MUTED = Color.rgb(135, 154, 194);

        private final Random random = new Random();
        private final Paint p = new Paint(Paint.ANTI_ALIAS_FLAG);
        private final Paint background = new Paint();
        private final Typeface face = Typeface.create("sans-serif", Typeface.NORMAL);
        private final Typeface bold = Typeface.create("sans-serif-medium", Typeface.BOLD);
        private final Typeface titleFace = Typeface.create("sans-serif-condensed", Typeface.BOLD);
        private final ArrayList<Particle> particles = new ArrayList<>();
        private final ArrayList<Mine> mines = new ArrayList<>();
        private final ArrayList<Trace> trail = new ArrayList<>();
        private final ArrayList<Spark> sky = new ArrayList<>();
        private final SharedPreferences prefs;

        private float w, h, d, fieldTop, fieldBottom;
        private int mode = READY, score = 0, best, lives = 3, collected = 0, combo = 0;
        private float timeLeft = 60f, playTime, lastCollect = -100f, fever, invincible;
        private float flash, shake, ambient, targetX, targetY;
        private float ballRadius, gravityRadius;
        private long lastFrameNs = 0L;
        private boolean holding = false, sound = true, gameReady = false;
        private OrbitPhysics.Body player;
        private Prize prize;

        GameSurface(Context ctx) {
            super(ctx);
            d = getResources().getDisplayMetrics().density;
            prefs = ctx.getSharedPreferences("neon_orbit_game", Context.MODE_PRIVATE);
            best = prefs.getInt("best", 0);
            sound = prefs.getBoolean("sound", true);
            setLayerType(View.LAYER_TYPE_HARDWARE, null);
            setClickable(true);
        }

        @Override protected void onSizeChanged(int width, int height, int oldW, int oldH) {
            super.onSizeChanged(width, height, oldW, oldH);
            w = width; h = height;
            fieldTop = 145f * d;
            fieldBottom = Math.max(fieldTop + 160f * d, h - 98f * d);
            ballRadius = 12f * d;
            gravityRadius = 17f * d;
            background.setShader(new LinearGradient(0, 0, w * .7f, h,
                Color.rgb(11, 20, 46), DARK, Shader.TileMode.CLAMP));
            sky.clear();
            for (int i = 0; i < 75; i++) {
                sky.add(new Spark(random.nextFloat() * w,
                    random.nextFloat() * h, .4f + random.nextFloat() * 1.45f,
                    random.nextFloat() * 6.28f));
            }
            player = new OrbitPhysics.Body(w * .5f, (fieldTop + fieldBottom) * .5f, ballRadius);
            targetX = player.x; targetY = player.y;
            prize = new Prize(w * .73f, fieldTop + (fieldBottom - fieldTop) * .30f, GOLD);
            gameReady = true;
        }

        void hostPause() {
            holding = false;
            if (mode == PLAY) mode = PAUSE;
            lastFrameNs = 0L;
        }
        void hostResume() { lastFrameNs = 0L; invalidate(); }

        private void start() {
            if (!gameReady) return;
            mode = PLAY;
            score = 0; lives = 3; collected = 0; combo = 0;
            timeLeft = 60f; playTime = 0f; lastCollect = -100f;
            fever = 0f; invincible = 0f; flash = 0f; shake = 0f;
            holding = false;
            mines.clear(); particles.clear(); trail.clear();
            player = new OrbitPhysics.Body(w * .5f,
                fieldTop + (fieldBottom - fieldTop) * .58f, ballRadius);
            targetX = player.x; targetY = player.y;
            spawnPrize();
            addMine(); addMine();
            playSound(ToneGenerator.TONE_PROP_ACK, 90);
        }

        private void finish() {
            if (mode != PLAY) return;
            mode = FINISH;
            holding = false;
            if (score > best) best = score;
            prefs.edit().putInt("best", best).apply();
            burst(player.x, player.y, BLUE, 36);
            playSound(ToneGenerator.TONE_PROP_NACK, 220);
        }

        private float rand(float a, float b) { return a + random.nextFloat() * (b - a); }
        private float clamp(float v, float lo, float hi) { return Math.max(lo, Math.min(hi, v)); }
        private float distance(float ax, float ay, float bx, float by) {
            return (float) Math.hypot(ax - bx, ay - by);
        }

        private void spawnPrize() {
            int type = random.nextFloat() < .12f ? CLOCK :
                       random.nextFloat() < .17f ? FEVER : GOLD;
            float x = w * .5f, y = (fieldTop + fieldBottom) * .5f;
            for (int tries = 0; tries < 100; tries++) {
                x = rand(46f * d, w - 46f * d);
                y = rand(fieldTop + 42f * d, fieldBottom - 42f * d);
                if (distance(x, y, player.x, player.y) < 120f * d) continue;
                boolean safe = true;
                for (Mine m : mines) {
                    if (distance(x, y, m.body.x, m.body.y) < 66f * d) { safe = false; break; }
                }
                if (safe) break;
            }
            prize = new Prize(x, y, type);
        }

        private void addMine() {
            if (mines.size() >= 7) return;
            float x = w * .25f, y = fieldTop + 60f * d;
            float r = rand(14f, 19f) * d;
            for (int tries = 0; tries < 90; tries++) {
                x = rand(r + 25f * d, w - r - 25f * d);
                y = rand(fieldTop + 30f * d, fieldBottom - 30f * d);
                if (distance(x, y, player.x, player.y) < 130f * d) continue;
                if (prize != null && distance(x, y, prize.x, prize.y) < 90f * d) continue;
                boolean safe = true;
                for (Mine old : mines) {
                    if (distance(x, y, old.body.x, old.body.y) < 60f * d) { safe = false; break; }
                }
                if (safe) break;
            }
            OrbitPhysics.Body body = new OrbitPhysics.Body(x, y, r);
            float a = rand(0f, 6.28f);
            float speed = rand(48f, 90f) * d;
            body.vx = (float) Math.cos(a) * speed;
            body.vy = (float) Math.sin(a) * speed;
            mines.add(new Mine(body, rand(0f, 6.28f), random.nextBoolean() ? 1 : -1));
        }

        private void collect() {
            int oldKind = prize.kind;
            combo = OrbitPhysics.nextCombo(combo, playTime - lastCollect);
            lastCollect = playTime;
            collected++;
            if (oldKind == CLOCK) timeLeft = Math.min(90f, timeLeft + 5f);
            if (oldKind == FEVER) fever = Math.max(fever, 5f);
            int gain = OrbitPhysics.points(oldKind == GOLD ? 100 : 150, combo, fever > 0);
            score += gain;
            if (score > best) best = score;
            int color = oldKind == CLOCK ? LIME : oldKind == FEVER ? PINK : GOLDEN;
            burst(prize.x, prize.y, color, 28);
            flash = .12f;
            if (collected % 5 == 0 && mines.size() < 7) addMine();
            playSound(combo >= 5 ? ToneGenerator.TONE_SUP_CONFIRM : ToneGenerator.TONE_PROP_BEEP, 75);
            performHapticFeedback(HapticFeedbackConstants.KEYBOARD_TAP);
            spawnPrize();
        }

        private void hit(Mine m) {
            if (invincible > 0 || fever > 0) return;
            lives--;
            combo = 0;
            invincible = 1.65f;
            shake = .25f;
            flash = .22f;
            burst(player.x, player.y, RED, 31);
            player.vx = -player.vx * .5f + (player.x - m.body.x) * 2f;
            player.vy = -player.vy * .5f + (player.y - m.body.y) * 2f;
            playSound(ToneGenerator.TONE_PROP_NACK, 155);
            performHapticFeedback(HapticFeedbackConstants.LONG_PRESS);
            if (lives <= 0) finish();
        }

        private void burst(float x, float y, int color, int count) {
            for (int i = 0; i < count; i++) {
                float a = rand(0f, 6.2831855f);
                float sp = rand(60f, 330f) * d;
                particles.add(new Particle(x, y,
                    (float) Math.cos(a) * sp, (float) Math.sin(a) * sp,
                    rand(.30f, .84f), rand(1.3f, 3.8f) * d, color));
            }
            while (particles.size() > 260) particles.remove(0);
        }

        private void playSound(int tone, int ms) {
            if (!sound || tones == null) return;
            try { tones.startTone(tone, ms); } catch (RuntimeException ignored) { }
        }

        private void update(float dt) {
            if (dt <= 0f) return;
            ambient += dt;
            flash = Math.max(0f, flash - dt);
            shake = Math.max(0f, shake - dt);
            for (int i = particles.size() - 1; i >= 0; i--) {
                Particle part = particles.get(i);
                part.x += part.vx * dt;
                part.y += part.vy * dt;
                part.vx *= (float) Math.pow(.982, dt * 60);
                part.vy *= (float) Math.pow(.982, dt * 60);
                part.left -= dt;
                if (part.left <= 0f) particles.remove(i);
            }
            if (mode != PLAY) return;
            playTime += dt;
            timeLeft -= dt;
            fever = Math.max(0f, fever - dt);
            invincible = Math.max(0f, invincible - dt);
            if (timeLeft <= 0f) { timeLeft = 0f; finish(); return; }
            OrbitPhysics.stepPlayer(player, targetX, targetY, holding, dt,
                17f * d, fieldTop + 5f * d, w - 17f * d, fieldBottom - 5f * d);
            trail.add(new Trace(player.x, player.y));
            if (trail.size() > 26) trail.remove(0);
            for (Mine m : mines) {
                OrbitPhysics.Body b = m.body;
                b.x += b.vx * dt;
                b.y += b.vy * dt;
                if (b.x - b.radius < 15f * d) { b.x = 15f * d + b.radius; b.vx = Math.abs(b.vx); }
                if (b.x + b.radius > w - 15f * d) { b.x = w - 15f * d - b.radius; b.vx = -Math.abs(b.vx); }
                if (b.y - b.radius < fieldTop + 4f * d) {
                    b.y = fieldTop + 4f * d + b.radius; b.vy = Math.abs(b.vy);
                }
                if (b.y + b.radius > fieldBottom - 4f * d) {
                    b.y = fieldBottom - 4f * d - b.radius; b.vy = -Math.abs(b.vy);
                }
                m.angle += m.spin * dt;
            }
            OrbitPhysics.Body token = new OrbitPhysics.Body(prize.x, prize.y, 19f * d);
            if (OrbitPhysics.touching(player, token)) collect();
            for (Mine m : mines) {
                if (OrbitPhysics.touching(player, m.body)) { hit(m); break; }
            }
        }

        @Override protected void onDraw(Canvas c) {
            super.onDraw(c);
            long now = System.nanoTime();
            float dt = lastFrameNs == 0L ? 0f :
                clamp((now - lastFrameNs) / 1_000_000_000f, 0f, .035f);
            lastFrameNs = now;
            update(dt);
            c.drawRect(0, 0, w, h, background);
            drawGrid(c);
            drawSky(c);
            c.save();
            if (shake > 0) c.translate(rand(-6f, 6f) * d * shake * 4f,
                    rand(-6f, 6f) * d * shake * 4f);
            drawPlayfield(c);
            c.restore();
            drawHud(c);
            if (mode == READY) drawIntro(c);
            if (mode == PAUSE) drawPause(c);
            if (mode == FINISH) drawFinish(c);
            postInvalidateOnAnimation();
        }

        private void style(int color, int alpha, Paint.Style s, float stroke) {
            p.reset();
            p.setAntiAlias(true);
            p.setColor(color);
            p.setAlpha(Math.max(0, Math.min(255, alpha)));
            p.setStyle(s);
            p.setStrokeWidth(stroke);
            p.setStrokeCap(Paint.Cap.ROUND);
            p.setStrokeJoin(Paint.Join.ROUND);
        }

        private void fillCircle(Canvas c, float x, float y, float rad, int color, int alpha) {
            style(color, alpha, Paint.Style.FILL, 1);
            c.drawCircle(x, y, rad, p);
        }
        private void ring(Canvas c, float x, float y, float rad,
                          int color, int alpha, float stroke) {
            style(color, alpha, Paint.Style.STROKE, stroke);
            c.drawCircle(x, y, rad, p);
        }
        private void text(Canvas c, String s, float x, float y, float size,
                          int color, int alpha, Typeface type, Paint.Align align) {
            style(color, alpha, Paint.Style.FILL, 0);
            p.setTypeface(type);
            p.setTextSize(size * d);
            p.setTextAlign(align);
            c.drawText(s, x, y, p);
        }
        private void center(Canvas c, String s, float x, float y, float size, int color) {
            text(c, s, x, y, size, color, 255, bold, Paint.Align.CENTER);
        }
        private void panel(Canvas c, float l, float t, float r, float b,
                           float corner, int color, int alpha) {
            style(color, alpha, Paint.Style.FILL, 1);
            c.drawRoundRect(l, t, r, b, corner, corner, p);
        }

        private void drawGrid(Canvas c) {
            style(Color.rgb(55, 88, 137), 27, Paint.Style.STROKE, .7f * d);
            float step = 45f * d;
            float xOffset = (ambient * 3.0f * d) % step;
            for (float x = xOffset; x < w; x += step) c.drawLine(x, 0, x, h, p);
            for (float y = 0; y < h; y += step) c.drawLine(0, y, w, y, p);
            style(Color.rgb(20, 67, 125), 80, Paint.Style.STROKE, 1f * d);
            c.drawLine(19f * d, fieldTop, w - 19f * d, fieldTop, p);
            c.drawLine(19f * d, fieldBottom, w - 19f * d, fieldBottom, p);
        }

        private void drawSky(Canvas c) {
            for (Spark s : sky) {
                int alpha = (int) (44f + 58f * (.5f + .5f * (float) Math.sin(ambient * .8f + s.phase)));
                fillCircle(c, s.x, s.y, s.r * d, WHITE, alpha);
            }
        }

        private void drawPlayfield(Canvas c) {
            if (fever > 0f && mode == PLAY) {
                float pulse = (float) Math.sin(ambient * 6);
                panel(c, 0, fieldTop, w, fieldBottom, 0, PINK, (int) (12 + pulse * 5));
            }
            if (holding && mode == PLAY) drawGravity(c);
            for (Trace t : trail) {
                int i = trail.indexOf(t);
                float ratio = (float) (i + 1) / Math.max(1, trail.size());
                float rad = (3f + ratio * 13f) * d;
                fillCircle(c, t.x, t.y, rad * .6f, BLUE, (int) (ratio * ratio * 65f));
            }
            for (Particle part : particles) {
                float u = clamp(part.left / part.total, 0, 1);
                fillCircle(c, part.x, part.y, part.r * 2.5f * u, part.color,
                    (int) (32f * u));
                fillCircle(c, part.x, part.y, part.r * Math.max(.2f, u), part.color,
                    (int) (230f * u));
            }
            for (Mine m : mines) drawMine(c, m);
            if (prize != null) drawPrize(c);
            if (player != null) drawPlayer(c);
            if (flash > 0f) {
                panel(c, 0, fieldTop, w, fieldBottom, 0,
                    invincible > 0f ? RED : WHITE, (int) (flash * 100f));
            }
        }

        private void drawGravity(Canvas c) {
            float pulse = (ambient * 85f * d) % (115f * d);
            for (int i = 0; i < 3; i++) {
                float r = 20f * d + (pulse + i * 38f * d) % (128f * d);
                int a = (int) (110f * (1f - (r - 20f * d) / (128f * d)));
                ring(c, targetX, targetY, r, PINK, a, 1.6f * d);
            }
            style(PINK, 90, Paint.Style.STROKE, 1f * d);
            c.drawLine(player.x, player.y, targetX, targetY, p);
            fillCircle(c, targetX, targetY, gravityRadius, PINK, 18);
            ring(c, targetX, targetY, gravityRadius * .76f, PINK, 180, 1.8f * d);
            ring(c, targetX, targetY, 4f * d, WHITE, 180, 1.2f * d);
        }

        private void drawPlayer(Canvas c) {
            if (invincible > 0f && (int) (ambient * 13) % 2 == 0) return;
            float pulse = .5f + .5f * (float) Math.sin(ambient * 5f);
            float r = player.radius;
            fillCircle(c, player.x, player.y, r * 2.8f + pulse * 4f * d, BLUE, 12);
            fillCircle(c, player.x, player.y, r * 2.0f, BLUE, 25);
            ring(c, player.x, player.y, r * 1.53f, BLUE, 120, 1.2f * d);
            fillCircle(c, player.x, player.y, r, BLUE, 255);
            fillCircle(c, player.x - r * .2f, player.y - r * .25f, r * .42f, WHITE, 242);
            if (fever > 0f) ring(c, player.x, player.y, r * 1.95f, PINK, 220, 2.1f * d);
            if (invincible > 0f) ring(c, player.x, player.y, r * 2.15f, GOLDEN, 210, 1.8f * d);
        }

        private void drawPrize(Canvas c) {
            float pulse = .5f + .5f * (float) Math.sin(ambient * 4.3f);
            int color = prize.kind == CLOCK ? LIME : prize.kind == FEVER ? PINK : GOLDEN;
            fillCircle(c, prize.x, prize.y, (26f + pulse * 7f) * d, color, 20);
            ring(c, prize.x, prize.y, (21f + pulse * 4f) * d, color, 110, 1.6f * d);
            drawStarShape(c, prize.x, prize.y, (12f + pulse * 1.6f) * d,
                    color, 255, ambient * .22f);
            fillCircle(c, prize.x, prize.y, 3.7f * d, WHITE, 255);
            if (prize.kind == CLOCK) {
                text(c, "+5s", prize.x, prize.y + 36f * d, 11, LIME,
                    220, bold, Paint.Align.CENTER);
            } else if (prize.kind == FEVER) {
                text(c, "2×", prize.x, prize.y + 36f * d, 11, PINK,
                    240, bold, Paint.Align.CENTER);
            }
        }

        private void drawStarShape(Canvas c, float x, float y, float rad,
                                   int color, int alpha, float rot) {
            Path path = new Path();
            for (int i = 0; i < 10; i++) {
                float a = (float) (-Math.PI / 2 + i * Math.PI / 5 + rot);
                float r = i % 2 == 0 ? rad : rad * .47f;
                float xx = x + (float) Math.cos(a) * r;
                float yy = y + (float) Math.sin(a) * r;
                if (i == 0) path.moveTo(xx, yy); else path.lineTo(xx, yy);
            }
            path.close();
            style(color, alpha, Paint.Style.FILL, 1f);
            c.drawPath(path, p);
        }

        private void drawMine(Canvas c, Mine mine) {
            OrbitPhysics.Body b = mine.body;
            float rr = b.radius;
            fillCircle(c, b.x, b.y, rr * 1.9f, RED, 22);
            ring(c, b.x, b.y, rr * 1.28f, RED, 135, 1.1f * d);
            for (int i = 0; i < 8; i++) {
                float a = mine.angle + i * (float) Math.PI / 4;
                float xx = (float) Math.cos(a), yy = (float) Math.sin(a);
                style(RED, 185, Paint.Style.STROKE, 3.2f * d);
                c.drawLine(b.x + xx * rr * .7f, b.y + yy * rr * .7f,
                           b.x + xx * rr * 1.47f, b.y + yy * rr * 1.47f, p);
            }
            fillCircle(c, b.x, b.y, rr * .78f, RED, 230);
            ring(c, b.x, b.y, rr * .46f, WHITE, 180, 1.2f * d);
            fillCircle(c, b.x, b.y, rr * .15f, DARK, 235);
        }

        private void drawHud(Canvas c) {
            panel(c, 0, 0, w, fieldTop - 5f * d, 0, Color.rgb(5, 11, 29), 235);
            float right = w - 20f * d;
            text(c, "SCORE", 23f * d, 34f * d, 10, MUTED, 240,
                bold, Paint.Align.LEFT);
            text(c, String.format(Locale.US, "%06d", score), 22f * d, 63f * d,
                25, WHITE, 255, titleFace, Paint.Align.LEFT);
            text(c, "TIME", w * .57f, 34f * d, 10, MUTED, 240,
                bold, Paint.Align.CENTER);
            text(c, String.format(Locale.US, "%04.1f", timeLeft), w * .57f,
                63f * d, 25, timeLeft < 10 && mode == PLAY ? RED : BLUE,
                255, titleFace, Paint.Align.CENTER);
            text(c, "BEST " + String.format(Locale.US, "%06d", best),
                right, 31f * d, 10, MUTED, 215, bold, Paint.Align.RIGHT);
            for (int i = 0; i < 3; i++) {
                int color = i < lives ? RED : Color.rgb(39, 53, 78);
                fillCircle(c, 28f * d + i * 22f * d, 93f * d, 6f * d, color, 240);
            }
            text(c, "SFX " + (sound ? "ON" : "OFF"), w - 113f * d, 98f * d,
                10, sound ? LIME : MUTED, 230, bold, Paint.Align.CENTER);
            text(c, "Ⅱ", w - 32f * d, 100f * d, 22, WHITE, 245,
                titleFace, Paint.Align.CENTER);
            style(Color.rgb(51, 69, 106), 180, Paint.Style.FILL, 1f);
            c.drawRoundRect(18f * d, 125f * d, w - 18f * d, 128f * d, 1.5f * d, 1.5f * d, p);
            style(fever > 0 ? PINK : BLUE, 245, Paint.Style.FILL, 1);
            float pct = clamp(timeLeft / 60f, 0f, 1f);
            c.drawRoundRect(18f * d, 125f * d,
                18f * d + (w - 36f * d) * pct, 128f * d, 1.5f * d, 1.5f * d, p);
            if (mode == PLAY) {
                if (fever > 0f) {
                    text(c, String.format(Locale.US, "FEVER ×2  %.1fs", fever), w*.5f,
                        fieldBottom + 26f * d, 15, PINK, 255, bold, Paint.Align.CENTER);
                } else if (combo > 1 && playTime - lastCollect < 4f) {
                    text(c, "COMBO  ×" + combo, w * .5f, fieldBottom + 26f * d,
                        16, GOLDEN, 255, titleFace, Paint.Align.CENTER);
                } else {
                    text(c, "WAVE " + String.format(Locale.US, "%02d", collected / 5 + 1),
                        w * .5f, fieldBottom + 26f * d, 12, MUTED, 220,
                        bold, Paint.Align.CENTER);
                }
            }
            text(c, "HOLD + DRAG", w * .5f, h - 43f * d, 12, BLUE,
                230, bold, Paint.Align.CENTER);
            text(c, "指の位置に引力を発生させる", w * .5f, h - 22f * d,
                12, MUTED, 225, face, Paint.Align.CENTER);
        }

        private void drawDim(Canvas c) {
            panel(c, 0, 0, w, h, 0, DARK, 223);
        }
        private void button(Canvas c, String label, float y) {
            float l = 42f * d, r = w - 42f * d;
            panel(c, l - 3f*d, y - 2f*d, r + 3f*d, y + 58f*d,
                19f*d, BLUE, 45);
            panel(c, l, y, r, y + 54f*d, 17f*d, BLUE, 242);
            center(c, label, w * .5f, y + 35f*d, 20, DARK);
        }

        private void drawIntro(Canvas c) {
            drawDim(c);
            float cy = h * .35f;
            for (int i = 0; i < 4; i++) {
                float a = ambient * (i % 2 == 0 ? .58f : -.48f) + i * 1.57f;
                float rr = 49f*d + i * 10f*d;
                ring(c, w*.5f, cy - 12f*d, rr, i%2==0 ? BLUE : PINK,
                    66 + 28 * (3 - i), 1.8f*d);
                fillCircle(c, w*.5f + (float)Math.cos(a)*rr,
                    cy - 12f*d + (float)Math.sin(a)*rr, (4f + (i%2)*2f)*d,
                    i%2==0 ? BLUE : PINK, 220);
            }
            fillCircle(c, w*.5f, cy - 12f*d, 17f*d, WHITE, 240);
            text(c, "NEON", w*.5f, h*.51f, 57, WHITE, 255,
                titleFace, Paint.Align.CENTER);
            text(c, "ORBIT", w*.5f, h*.575f, 58, BLUE, 255,
                titleFace, Paint.Align.CENTER);
            text(c, "重力で、星を奪え。", w*.5f, h*.624f, 15,
                MUTED, 255, bold, Paint.Align.CENTER);
            button(c, "START  ▶", h*.685f);
            text(c, "HOLD + DRAG で球を引き寄せよう", w*.5f, h*.83f,
                12, WHITE, 220, face, Paint.Align.CENTER);
            text(c, "星を集めろ。機雷を避けろ。60秒勝負。", w*.5f,
                h*.857f, 12, MUTED, 225, face, Paint.Align.CENTER);
            text(c, "OFFLINE  •  NO ADS  •  ONE FINGER", w*.5f,
                h*.92f, 10, BLUE, 175, bold, Paint.Align.CENTER);
        }

        private void drawPause(Canvas c) {
            drawDim(c);
            text(c, "PAUSED", w*.5f, h*.43f, 52, WHITE, 255,
                titleFace, Paint.Align.CENTER);
            text(c, "指を休めても、宇宙は逃げない。", w*.5f, h*.49f,
                13, MUTED, 245, face, Paint.Align.CENTER);
            button(c, "RESUME  ▶", h*.56f);
        }

        private void drawFinish(Canvas c) {
            drawDim(c);
            text(c, lives <= 0 ? "GAME OVER" : "TIME UP", w*.5f,
                h*.325f, 49, WHITE, 255, titleFace, Paint.Align.CENTER);
            text(c, "FINAL SCORE", w*.5f, h*.398f, 12, MUTED,
                255, bold, Paint.Align.CENTER);
            text(c, String.format(Locale.US, "%06d", score), w*.5f, h*.49f,
                59, GOLDEN, 255, titleFace, Paint.Align.CENTER);
            text(c, "BEST  " + String.format(Locale.US, "%06d", best),
                w*.5f, h*.542f, 17, BLUE, 250, bold, Paint.Align.CENTER);
            text(c, "STARS COLLECTED  " + collected, w*.5f, h*.592f,
                12, MUTED, 240, face, Paint.Align.CENTER);
            button(c, "RETRY  ↻", h*.67f);
            text(c, "コンボをつなげて最高得点を更新", w*.5f,
                h*.811f, 12, WHITE, 210, face, Paint.Align.CENTER);
        }

        @Override public boolean onTouchEvent(MotionEvent e) {
            float x = e.getX(), y = e.getY();
            int action = e.getActionMasked();
            if (action == MotionEvent.ACTION_DOWN) {
                if (mode == READY || mode == FINISH) { start(); invalidate(); return true; }
                if (mode == PAUSE) { mode = PLAY; holding = false; invalidate(); return true; }
                if (mode == PLAY && y < 122f * d && x > w - 65f * d) {
                    mode = PAUSE; holding = false; invalidate(); return true;
                }
                if (mode == PLAY && y < 122f * d && x > w - 153f*d) {
                    sound = !sound;
                    prefs.edit().putBoolean("sound", sound).apply();
                    if (sound) playSound(ToneGenerator.TONE_PROP_ACK, 80);
                    invalidate(); return true;
                }
                holding = true;
                targetX = clamp(x, 20f*d, w - 20f*d);
                targetY = clamp(y, fieldTop + 20f*d, fieldBottom - 20f*d);
                invalidate(); return true;
            }
            if (action == MotionEvent.ACTION_MOVE) {
                if (mode == PLAY && holding) {
                    targetX = clamp(x, 20f*d, w - 20f*d);
                    targetY = clamp(y, fieldTop + 20f*d, fieldBottom - 20f*d);
                }
                return true;
            }
            if (action == MotionEvent.ACTION_UP || action == MotionEvent.ACTION_CANCEL) {
                holding = false;
                invalidate(); return true;
            }
            return true;
        }

        private final class Prize {
            final float x, y;
            final int kind;
            Prize(float x, float y, int kind) { this.x = x; this.y = y; this.kind = kind; }
        }
        private final class Mine {
            final OrbitPhysics.Body body;
            float angle;
            final float spin;
            Mine(OrbitPhysics.Body body, float angle, float spin) {
                this.body = body; this.angle = angle; this.spin = spin;
            }
        }
        private final class Trace {
            final float x, y;
            Trace(float x, float y) { this.x = x; this.y = y; }
        }
        private final class Particle {
            float x, y, vx, vy, left;
            final float total, r;
            final int color;
            Particle(float x, float y, float vx, float vy, float total,
                     float radius, int color) {
                this.x = x; this.y = y; this.vx = vx; this.vy = vy;
                this.total = total; this.left = total; this.r = radius; this.color = color;
            }
        }
        private final class Spark {
            final float x, y, r, phase;
            Spark(float x, float y, float r, float phase) {
                this.x = x; this.y = y; this.r = r; this.phase = phase;
            }
        }
    }
}
