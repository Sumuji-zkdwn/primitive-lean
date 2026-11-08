package com.primitive.curvelab;

import android.app.Activity;
import android.app.AlertDialog;
import android.content.Intent;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.Path;
import android.graphics.Typeface;
import android.graphics.drawable.GradientDrawable;
import android.net.Uri;
import android.os.Bundle;
import android.view.MotionEvent;
import android.view.View;
import android.view.ViewGroup;
import android.widget.Button;
import android.widget.HorizontalScrollView;
import android.widget.LinearLayout;
import android.widget.TextView;
import android.widget.Toast;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Locale;

/** Offline pocket geometry laboratory, built with the Android framework only. */
public class MainActivity extends Activity {
    private static final int BG = Color.rgb(17, 20, 24);
    private static final int PANEL = Color.rgb(25, 31, 36);
    private static final int PANEL_SOFT = Color.rgb(31, 38, 43);
    private static final int FG = Color.rgb(238, 240, 230);
    private static final int MUTED = Color.rgb(155, 168, 165);
    private static final int GREEN = Color.rgb(188, 235, 167);
    private static final int ORANGE = Color.rgb(255, 169, 108);
    private static final int BLUE = Color.rgb(102, 191, 237);
    private static final int[] STROKE_COLORS = {
            GREEN, ORANGE, BLUE, Color.rgb(208, 159, 231), Color.rgb(247, 216, 132)
    };
    private static final int SAVE_CSV = 11;
    private static final int SAVE_PNG = 12;

    private SketchView sketch;
    private GraphView graphs;
    private TextView metrics;
    private Button drawButton, observeButton;
    private boolean drawMode = true;

    private int dp(float size) {
        return (int) (size * getResources().getDisplayMetrics().density + 0.5f);
    }

    private TextView text(String message, int sp, int color) {
        TextView view = new TextView(this);
        view.setText(message);
        view.setTextColor(color);
        view.setTextSize(sp);
        view.setIncludeFontPadding(false);
        return view;
    }

    private GradientDrawable background(int color, int radius) {
        GradientDrawable bg = new GradientDrawable();
        bg.setColor(color);
        bg.setCornerRadius(dp(radius));
        return bg;
    }

    private Button button(String label) {
        Button b = new Button(this);
        b.setText(label);
        b.setTextColor(FG);
        b.setTextSize(13);
        b.setAllCaps(false);
        b.setPadding(dp(14), dp(4), dp(14), dp(4));
        b.setMinimumHeight(dp(42));
        b.setMinWidth(0);
        b.setBackground(background(PANEL_SOFT, 12));
        b.setElevation(0);
        return b;
    }

    private void addToRow(LinearLayout row, Button button) {
        LinearLayout.LayoutParams lp = new LinearLayout.LayoutParams(
                ViewGroup.LayoutParams.WRAP_CONTENT, dp(42));
        lp.setMarginEnd(dp(7));
        row.addView(button, lp);
    }

    @Override
    public void onCreate(Bundle state) {
        super.onCreate(state);
        getWindow().setStatusBarColor(BG);
        getWindow().setNavigationBarColor(BG);

        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setBackgroundColor(BG);
        root.setPadding(dp(14), dp(13), dp(14), dp(10));
        setContentView(root);

        TextView title = text("曲線実験室", 26, FG);
        title.setTypeface(Typeface.create("sans-serif-medium", Typeface.NORMAL));
        root.addView(title);
        TextView subtitle = text("DRAW → OBSERVE   /   曲線から高さと曲率を読む", 11, MUTED);
        LinearLayout.LayoutParams subtitleLp = new LinearLayout.LayoutParams(-1, -2);
        subtitleLp.topMargin = dp(5);
        subtitleLp.bottomMargin = dp(13);
        root.addView(subtitle, subtitleLp);

        LinearLayout tools = new LinearLayout(this);
        tools.setOrientation(LinearLayout.HORIZONTAL);
        drawButton = button("✎  描く");
        observeButton = button("⊙  観測");
        Button undo = button("↶  戻す");
        Button clear = button("消す");
        addToRow(tools, drawButton);
        addToRow(tools, observeButton);
        addToRow(tools, undo);
        addToRow(tools, clear);
        HorizontalScrollView scroller = new HorizontalScrollView(this);
        scroller.setHorizontalScrollBarEnabled(false);
        scroller.addView(tools);
        LinearLayout.LayoutParams toolLp = new LinearLayout.LayoutParams(-1, dp(42));
        toolLp.bottomMargin = dp(10);
        root.addView(scroller, toolLp);

        sketch = new SketchView();
        sketch.setContentDescription("曲線キャンバス。描くモードで指を動かすと曲線を描画。観測モードでは曲線をなぞると接線と高さを測定");
        sketch.setBackground(background(PANEL, 18));
        sketch.setClipToOutline(true);
        LinearLayout.LayoutParams sketchLp = new LinearLayout.LayoutParams(-1, 0, 1.0f);
        sketchLp.bottomMargin = dp(11);
        root.addView(sketch, sketchLp);

        metrics = text("曲線を指で描いてください。", 13, FG);
        metrics.setTypeface(Typeface.create("monospace", Typeface.NORMAL));
        metrics.setPadding(dp(11), dp(9), dp(10), dp(8));
        metrics.setBackground(background(PANEL, 12));
        metrics.setMinHeight(dp(68));
        LinearLayout.LayoutParams metricsLp = new LinearLayout.LayoutParams(-1, -2);
        metricsLp.bottomMargin = dp(10);
        root.addView(metrics, metricsLp);

        graphs = new GraphView();
        graphs.setBackground(background(PANEL, 14));
        graphs.setClipToOutline(true);
        LinearLayout.LayoutParams graphLp = new LinearLayout.LayoutParams(-1, dp(176));
        graphLp.bottomMargin = dp(9);
        root.addView(graphs, graphLp);

        LinearLayout saveRow = new LinearLayout(this);
        saveRow.setOrientation(LinearLayout.HORIZONTAL);
        Button csv = button("CSV を保存");
        Button png = button("PNG を保存");
        Button help = button("？");
        addToRow(saveRow, csv);
        addToRow(saveRow, png);
        addToRow(saveRow, help);
        root.addView(saveRow);

        drawButton.setOnClickListener(v -> setMode(true));
        observeButton.setOnClickListener(v -> setMode(false));
        undo.setOnClickListener(v -> sketch.undo());
        clear.setOnClickListener(v -> new AlertDialog.Builder(this)
                .setTitle("キャンバスを消去")
                .setMessage("描いたすべての曲線を消しますか？")
                .setNegativeButton("やめる", null)
                .setPositiveButton("消す", (dialog, which) -> sketch.erase())
                .show());
        csv.setOnClickListener(v -> createDocument("text/csv", "curve-lab.csv", SAVE_CSV));
        png.setOnClickListener(v -> createDocument("image/png", "curve-lab.png", SAVE_PNG));
        help.setOnClickListener(v -> help());

        if (state != null && state.containsKey("tracks")) {
            sketch.restore(state.getString("tracks", ""));
            drawMode = state.getBoolean("drawMode", true);
            sketch.anchor = state.getInt("anchor", sketch.anchor);
            sketch.selected = state.getInt("selected", sketch.selected);
            sketch.clampSelection();
        }
        setMode(drawMode);
        refresh();
    }

    private void help() {
        new AlertDialog.Builder(this)
            .setTitle("何が見える？")
            .setMessage("「描く」で曲線を追加し、「観測」で曲線の好きな位置をなぞります。" +
                "\n\nその点の接線に垂直な方向から測った高さを H とすると、弧長 s を使って H(0)=H′(0)=0、" +
                "H″(0)=κ(0) が成立します。\n\n上のグラフは選んだ基準点からの高さ H、" +
                "下のグラフは符号付き曲率 κ を描いています。" +
                "\n\n表示値は離散点を平滑化した有限差分の近似値です。" +
                "長さの単位は画面の dp。ネット通信や特別な権限は使いません。")
            .setPositiveButton("閉じる", null)
            .show();
    }

    private void setMode(boolean isDraw) {
        drawMode = isDraw;
        drawButton.setBackground(background(isDraw ? GREEN : PANEL_SOFT, 12));
        drawButton.setTextColor(isDraw ? BG : FG);
        observeButton.setBackground(background(isDraw ? PANEL_SOFT : GREEN, 12));
        observeButton.setTextColor(isDraw ? FG : BG);
        sketch.invalidate();
    }

    private void refresh() {
        if (metrics == null || sketch == null) return;
        sketch.clampSelection();
        Geometry.Track track = sketch.currentTrack();
        if (track == null || track.size() < 3) {
            metrics.setText("まだ曲線がありません。\n「描く」で指を動かしてください。");
        } else {
            int anchor = sketch.anchor;
            double density = getResources().getDisplayMetrics().density;
            double k = track.curvature[anchor] * 100.0 * density;
            double h2 = Geometry.heightSecondDerivative(track, anchor) * 100.0 * density;
            metrics.setText(String.format(Locale.JAPAN,
                    "線 %d/%d    全長 %.0f dp    基準 %.0f dp\n100dp·κ  %+.3f       100dp·H″  %+.3f",
                    sketch.selected + 1, sketch.strokes.size(), track.length() / density,
                    track.arc[anchor] / density, k, h2));
        }
        if (graphs != null) graphs.invalidate();
        sketch.invalidate();
    }

    private void createDocument(String mime, String name, int requestCode) {
        if (sketch.strokes.isEmpty()) {
            Toast.makeText(this, "先に曲線を描いてください", Toast.LENGTH_SHORT).show();
            return;
        }
        Intent intent = new Intent(Intent.ACTION_CREATE_DOCUMENT);
        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType(mime);
        intent.putExtra(Intent.EXTRA_TITLE, name);
        startActivityForResult(intent, requestCode);
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        super.onActivityResult(requestCode, resultCode, data);
        if (resultCode != RESULT_OK || data == null || data.getData() == null) return;
        Uri uri = data.getData();
        try (OutputStream stream = getContentResolver().openOutputStream(uri)) {
            if (stream == null) throw new IllegalStateException("保存先を開けません");
            if (requestCode == SAVE_CSV) {
                try (Writer writer = new OutputStreamWriter(stream, StandardCharsets.UTF_8)) {
                    writer.write('\ufeff');
                    writer.write("stroke,index,s_dp,x_dp,y_dp,curvature_per_dp,height_from_selected_anchor_dp\n");
                    double density = getResources().getDisplayMetrics().density;
                    for (int t = 0; t < sketch.strokes.size(); t++) {
                        Geometry.Track track = sketch.strokes.get(t).track;
                        for (int i = 0; i < track.size(); i++) {
                            Geometry.Point p = track.points.get(i);
                            String height = t == sketch.selected
                                    ? String.format(Locale.US, "%.6f", Geometry.height(track, sketch.anchor, i) / density)
                                    : "";
                            writer.write(String.format(Locale.US,
                                    "%d,%d,%.6f,%.6f,%.6f,%.8f,%s\n", t + 1, i,
                                    track.arc[i] / density, p.x / density, p.y / density,
                                    track.curvature[i] * density, height));
                        }
                    }
                }
            } else if (requestCode == SAVE_PNG) {
                int w = sketch.getWidth();
                int h = sketch.getHeight() + graphs.getHeight();
                if (w <= 0 || h <= 0) throw new IllegalStateException("画像サイズが不正です");
                Bitmap bitmap = Bitmap.createBitmap(w, h, Bitmap.Config.ARGB_8888);
                try {
                    Canvas canvas = new Canvas(bitmap);
                    canvas.drawColor(BG);
                    sketch.draw(canvas);
                    canvas.save();
                    canvas.translate(0, sketch.getHeight());
                    graphs.draw(canvas);
                    canvas.restore();
                    if (!bitmap.compress(Bitmap.CompressFormat.PNG, 100, stream)) {
                        throw new IllegalStateException("PNG出力に失敗しました");
                    }
                } finally {
                    bitmap.recycle();
                }
            }
            Toast.makeText(this, "保存しました", Toast.LENGTH_SHORT).show();
        } catch (Exception e) {
            Toast.makeText(this, "保存できませんでした: " + e.getMessage(), Toast.LENGTH_LONG).show();
        }
    }

    @Override
    protected void onSaveInstanceState(Bundle out) {
        super.onSaveInstanceState(out);
        out.putString("tracks", sketch.serialize());
        out.putBoolean("drawMode", drawMode);
        out.putInt("anchor", sketch.anchor);
        out.putInt("selected", sketch.selected);
    }

    private static final class Stroke {
        final ArrayList<Geometry.Point> raw;
        final Geometry.Track track;
        Stroke(ArrayList<Geometry.Point> raw) {
            this.raw = raw;
            this.track = Geometry.analyze(raw);
        }
    }

    private final class SketchView extends View {
        final ArrayList<Stroke> strokes = new ArrayList<>();
        ArrayList<Geometry.Point> drawing;
        int selected = -1;
        int anchor = 0;
        boolean initialized = false;
        private final Paint pen = new Paint(Paint.ANTI_ALIAS_FLAG);

        SketchView() {
            super(MainActivity.this);
            setLayerType(View.LAYER_TYPE_SOFTWARE, null);
        }

        Geometry.Track currentTrack() {
            if (selected < 0 || selected >= strokes.size()) return null;
            return strokes.get(selected).track;
        }

        void clampSelection() {
            if (strokes.isEmpty()) { selected = -1; anchor = 0; return; }
            selected = Math.max(0, Math.min(selected, strokes.size() - 1));
            Geometry.Track track = currentTrack();
            anchor = Math.max(0, Math.min(anchor, track.size() - 1));
        }

        void addStroke(ArrayList<Geometry.Point> raw) {
            if (raw.size() < 3) return;
            if (strokes.size() >= 24) strokes.remove(0);
            strokes.add(new Stroke(raw));
            selected = strokes.size() - 1;
            anchor = strokes.get(selected).track.size() / 2;
            refresh();
        }

        @Override
        protected void onSizeChanged(int w, int h, int oldw, int oldh) {
            super.onSizeChanged(w, h, oldw, oldh);
            if (!initialized && w > 0 && h > 0) {
                initialized = true;
                ArrayList<Geometry.Point> demo = new ArrayList<>();
                for (int i = 0; i <= 80; i++) {
                    double t = i / 80.0;
                    double x = (0.09 + 0.82 * t) * w;
                    double y = (0.49 + 0.18 * Math.sin(t * Math.PI * 3.2)
                            + 0.065 * Math.cos(t * Math.PI * 6.1)) * h;
                    demo.add(new Geometry.Point(x, y));
                }
                addStroke(demo);
            }
        }

        void addSample(float x, float y) {
            if (drawing == null || drawing.isEmpty() || drawing.size() > 2400) return;
            Geometry.Point last = drawing.get(drawing.size() - 1);
            double gap = dp(5);
            double dist = Math.hypot(x - last.x, y - last.y);
            while (dist >= gap && drawing.size() <= 2400) {
                double f = gap / dist;
                last = new Geometry.Point(last.x + f * (x - last.x),
                        last.y + f * (y - last.y));
                drawing.add(last);
                dist = Math.hypot(x - last.x, y - last.y);
            }
        }

        @Override
        public boolean onTouchEvent(MotionEvent event) {
            float x = Math.max(0, Math.min(event.getX(), getWidth()));
            float y = Math.max(0, Math.min(event.getY(), getHeight()));
            int action = event.getActionMasked();
            if (drawMode) {
                if (action == MotionEvent.ACTION_DOWN) {
                    getParent().requestDisallowInterceptTouchEvent(true);
                    drawing = new ArrayList<>();
                    drawing.add(new Geometry.Point(x, y));
                    invalidate();
                    return true;
                }
                if (action == MotionEvent.ACTION_MOVE && drawing != null) {
                    for (int i = 0; i < event.getHistorySize(); i++) {
                        addSample(event.getHistoricalX(i), event.getHistoricalY(i));
                    }
                    addSample(x, y);
                    invalidate();
                    return true;
                }
                if (action == MotionEvent.ACTION_UP && drawing != null) {
                    addSample(x, y);
                    ArrayList<Geometry.Point> completed = drawing;
                    drawing = null;
                    addStroke(completed);
                    performClick();
                    invalidate();
                    return true;
                }
                if (action == MotionEvent.ACTION_CANCEL) {
                    drawing = null;
                    invalidate();
                    return true;
                }
            } else if (action == MotionEvent.ACTION_DOWN || action == MotionEvent.ACTION_MOVE || action == MotionEvent.ACTION_UP) {
                if (action == MotionEvent.ACTION_DOWN) getParent().requestDisallowInterceptTouchEvent(true);
                double nearest = Double.POSITIVE_INFINITY;
                int newSelected = selected;
                int newAnchor = anchor;
                for (int t = 0; t < strokes.size(); t++) {
                    Geometry.Track track = strokes.get(t).track;
                    int idx = Geometry.nearest(track, x, y);
                    Geometry.Point p = track.points.get(idx);
                    double d = (x - p.x) * (x - p.x) + (y - p.y) * (y - p.y);
                    if (d < nearest) { nearest = d; newSelected = t; newAnchor = idx; }
                }
                if (newSelected != selected || newAnchor != anchor) {
                    selected = newSelected;
                    anchor = newAnchor;
                    refresh();
                }
                if (action == MotionEvent.ACTION_UP) performClick();
                return true;
            }
            return super.onTouchEvent(event);
        }

        @Override
        public boolean performClick() {
            super.performClick();
            return true;
        }

        void undo() {
            if (!strokes.isEmpty()) strokes.remove(strokes.size() - 1);
            selected = strokes.size() - 1;
            anchor = selected >= 0 ? strokes.get(selected).track.size() / 2 : 0;
            refresh();
        }
        void erase() {
            strokes.clear();
            drawing = null;
            selected = -1;
            anchor = 0;
            initialized = true;
            refresh();
        }

        String serialize() {
            StringBuilder b = new StringBuilder();
            for (Stroke stroke : strokes) {
                if (b.length() > 0) b.append(';');
                for (int i = 0; i < stroke.raw.size(); i++) {
                    if (i > 0) b.append('|');
                    Geometry.Point p = stroke.raw.get(i);
                    b.append((float) p.x).append(',').append((float) p.y);
                }
            }
            return b.toString();
        }
        void restore(String serialized) {
            initialized = true;
            strokes.clear();
            if (!serialized.isEmpty()) {
                for (String strokeString : serialized.split(";")) {
                    ArrayList<Geometry.Point> raw = new ArrayList<>();
                    for (String pair : strokeString.split("\\|")) {
                        String[] xy = pair.split(",");
                        if (xy.length != 2) continue;
                        try {
                            raw.add(new Geometry.Point(Double.parseDouble(xy[0]),
                                    Double.parseDouble(xy[1])));
                        } catch (NumberFormatException ignored) { }
                    }
                    if (raw.size() >= 3) strokes.add(new Stroke(raw));
                }
            }
            selected = strokes.size() - 1;
            anchor = selected < 0 ? 0 : strokes.get(selected).track.size() / 2;
        }

        @Override
        protected void onDraw(Canvas canvas) {
            super.onDraw(canvas);
            int w = getWidth(), h = getHeight();
            pen.setStyle(Paint.Style.STROKE);
            pen.setStrokeWidth(dp(0.7f));
            pen.setColor(Color.rgb(38, 48, 53));
            int gap = dp(26);
            for (int x = gap; x < w; x += gap) canvas.drawLine(x, 0, x, h, pen);
            for (int y = gap; y < h; y += gap) canvas.drawLine(0, y, w, y, pen);
            for (int i = 0; i < strokes.size(); i++) {
                Geometry.Track track = strokes.get(i).track;
                if (track.size() == 0) continue;
                Path path = new Path();
                Geometry.Point first = track.points.get(0);
                path.moveTo((float) first.x, (float) first.y);
                for (int j = 1; j < track.size(); j++) {
                    Geometry.Point p = track.points.get(j);
                    path.lineTo((float) p.x, (float) p.y);
                }
                pen.setColor(STROKE_COLORS[i % STROKE_COLORS.length]);
                pen.setAlpha(i == selected ? 255 : 145);
                pen.setStyle(Paint.Style.STROKE);
                pen.setStrokeJoin(Paint.Join.ROUND);
                pen.setStrokeCap(Paint.Cap.ROUND);
                pen.setStrokeWidth(dp(i == selected ? 3.3f : 2.2f));
                canvas.drawPath(path, pen);
                pen.setAlpha(255);
            }
            if (drawing != null && !drawing.isEmpty()) {
                Path path = new Path();
                path.moveTo((float) drawing.get(0).x, (float) drawing.get(0).y);
                for (int i = 1; i < drawing.size(); i++) {
                    Geometry.Point p = drawing.get(i);
                    path.lineTo((float) p.x, (float) p.y);
                }
                pen.setStyle(Paint.Style.STROKE);
                pen.setColor(GREEN);
                pen.setStrokeWidth(dp(3));
                pen.setStrokeCap(Paint.Cap.ROUND);
                canvas.drawPath(path, pen);
            }
            if (currentTrack() != null && !drawMode) {
                Geometry.Track track = currentTrack();
                Geometry.Point o = track.points.get(anchor);
                Geometry.Point a = track.points.get(Math.max(0, anchor - 1));
                Geometry.Point b = track.points.get(Math.min(track.size() - 1, anchor + 1));
                double tx = b.x - a.x, ty = b.y - a.y;
                double length = Math.hypot(tx, ty);
                if (length > 1e-9) {
                    tx /= length; ty /= length;
                    float size = dp(28);
                    pen.setStrokeWidth(dp(1.6f));
                    pen.setColor(ORANGE);
                    canvas.drawLine((float) (o.x - size * tx), (float) (o.y - size * ty),
                            (float) (o.x + size * tx), (float) (o.y + size * ty), pen);
                    pen.setColor(BLUE);
                    canvas.drawLine((float) o.x, (float) o.y,
                            (float) (o.x + size * ty), (float) (o.y - size * tx), pen);
                }
                pen.setStyle(Paint.Style.FILL);
                pen.setColor(FG);
                canvas.drawCircle((float) o.x, (float) o.y, dp(5), pen);
                pen.setColor(PANEL);
                canvas.drawCircle((float) o.x, (float) o.y, dp(2), pen);
            }
            pen.setStyle(Paint.Style.FILL);
            pen.setTypeface(Typeface.create("monospace", Typeface.NORMAL));
            pen.setTextSize(dp(11));
            pen.setColor(MUTED);
            canvas.drawText(drawMode ? "01   DRAW" : "02   OBSERVE", dp(14), dp(25), pen);
            pen.setTextSize(dp(10));
            canvas.drawText(drawMode ? "指でなぞって曲線を追加" : "曲線上をスライドして基準点を選択",
                    dp(14), h - dp(15), pen);
        }
    }

    private final class GraphView extends View {
        private final Paint paint = new Paint(Paint.ANTI_ALIAS_FLAG);
        GraphView() { super(MainActivity.this); }
        private void line(Canvas c, int color, float stroke, float x1, float y1, float x2, float y2) {
            paint.setStyle(Paint.Style.STROKE);
            paint.setColor(color);
            paint.setStrokeWidth(dp(stroke));
            c.drawLine(x1, y1, x2, y2, paint);
        }
        private void label(Canvas c, String text, float x, float y, int color) {
            paint.setStyle(Paint.Style.FILL);
            paint.setTypeface(Typeface.create("monospace", Typeface.NORMAL));
            paint.setTextSize(dp(10));
            paint.setColor(color);
            c.drawText(text, x, y, paint);
        }
        private void plot(Canvas c, Geometry.Track track, double[] values,
                          float left, float right, float top, float bottom, int color) {
            int n = track.size();
            if (n < 2 || track.length() < 1e-6) return;
            double min = 0, max = 0;
            for (double v : values) {
                min = Math.min(min, v);
                max = Math.max(max, v);
            }
            double range = Math.max(1e-6, max - min);
            min -= range * 0.16;
            max += range * 0.16;
            range = max - min;
            float mid = (float) (bottom - (0 - min) / range * (bottom - top));
            line(c, Color.rgb(51, 62, 64), 0.6f, left, mid, right, mid);
            Path path = new Path();
            for (int i = 0; i < n; i++) {
                float x = left + (float) (track.arc[i] / track.length()) * (right - left);
                float y = (float) (bottom - ((values[i] - min) / range) * (bottom - top));
                if (i == 0) path.moveTo(x, y); else path.lineTo(x, y);
            }
            paint.setStyle(Paint.Style.STROKE);
            paint.setStrokeWidth(dp(1.8f));
            paint.setStrokeCap(Paint.Cap.ROUND);
            paint.setStrokeJoin(Paint.Join.ROUND);
            paint.setColor(color);
            c.drawPath(path, paint);
            float anchorX = left + (float) (track.arc[sketch.anchor] / track.length()) * (right - left);
            line(c, Color.rgb(130, 138, 133), 0.9f, anchorX, top, anchorX, bottom);
        }
        @Override
        protected void onDraw(Canvas canvas) {
            super.onDraw(canvas);
            float left = dp(16), right = getWidth() - dp(15);
            float top = dp(29), bottom = getHeight() - dp(13);
            float split = (top + bottom) * 0.53f;
            line(canvas, Color.rgb(50, 60, 62), 0.8f, left, split, right, split);
            label(canvas, "HEIGHT  H(s)", left, dp(17), ORANGE);
            label(canvas, "CURVATURE  κ(s)", left, split + dp(13), BLUE);
            Geometry.Track track = sketch == null ? null : sketch.currentTrack();
            if (track == null || track.size() < 3) return;
            double density = getResources().getDisplayMetrics().density;
            double[] heights = new double[track.size()];
            double[] curvatures = new double[track.size()];
            for (int i = 0; i < track.size(); i++) {
                heights[i] = Geometry.height(track, sketch.anchor, i) / density;
                curvatures[i] = track.curvature[i] * 100.0 * density;
            }
            plot(canvas, track, heights, left, right, top, split - dp(7), ORANGE);
            plot(canvas, track, curvatures, left, right, split + dp(19), bottom, BLUE);
        }
    }
}
