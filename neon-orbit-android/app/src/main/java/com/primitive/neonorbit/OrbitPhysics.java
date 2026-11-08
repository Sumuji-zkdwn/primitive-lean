package com.primitive.neonorbit;

/** Deterministic, Android-free motion and scoring rules. All positions are pixels. */
public final class OrbitPhysics {
    private OrbitPhysics() {}

    public static final class Body {
        public float x, y, vx, vy, radius;
        public Body(float x, float y, float radius) {
            this.x = x;
            this.y = y;
            this.radius = radius;
        }
    }

    public static void stepPlayer(Body b, float tx, float ty, boolean holding,
                                  float dt, float left, float top, float right, float bottom) {
        if (dt <= 0f) return;
        dt = Math.min(dt, 0.040f);
        if (holding) {
            // Spring-like gravitational field with a terminal speed.
            b.vx += (tx - b.x) * 8.2f * dt;
            b.vy += (ty - b.y) * 8.2f * dt;
        }
        float drag = (float) Math.pow(holding ? 0.987 : 0.994, dt * 60f);
        b.vx *= drag;
        b.vy *= drag;
        float speed = (float) Math.hypot(b.vx, b.vy);
        float max = 890f;
        if (speed > max) {
            b.vx *= max / speed;
            b.vy *= max / speed;
        }
        b.x += b.vx * dt;
        b.y += b.vy * dt;
        if (b.x - b.radius < left) {
            b.x = left + b.radius;
            b.vx = Math.abs(b.vx) * 0.48f;
        }
        if (b.x + b.radius > right) {
            b.x = right - b.radius;
            b.vx = -Math.abs(b.vx) * 0.48f;
        }
        if (b.y - b.radius < top) {
            b.y = top + b.radius;
            b.vy = Math.abs(b.vy) * 0.48f;
        }
        if (b.y + b.radius > bottom) {
            b.y = bottom - b.radius;
            b.vy = -Math.abs(b.vy) * 0.48f;
        }
    }

    public static boolean touching(Body a, Body b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        float r = a.radius + b.radius;
        return dx * dx + dy * dy <= r * r;
    }

    /** Collect within 4 seconds to continue a combo, with a maximum 8x multiplier. */
    public static int nextCombo(int oldCombo, float secondsSinceCollect) {
        return secondsSinceCollect <= 4f ? Math.min(8, oldCombo + 1) : 1;
    }

    public static int points(int base, int combo, boolean fever) {
        return base * Math.max(1, Math.min(8, combo)) * (fever ? 2 : 1);
    }
}
