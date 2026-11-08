package com.primitive.curvelab;

import java.util.ArrayList;
import java.util.List;

/**
 * Screen-space geometry. Screen y grows downward, so positive signed curvature
 * is counter-clockwise when the curve is viewed with mathematical y upward.
 * No Android dependencies: this class can be tested with plain javac/java.
 */
public final class Geometry {
    private Geometry() {}

    public static final class Point {
        public final double x;
        public final double y;
        public Point(double x, double y) { this.x = x; this.y = y; }
    }

    public static final class Track {
        public final ArrayList<Point> points;
        public final double[] arc;
        public final double[] curvature;

        private Track(ArrayList<Point> points, double[] arc, double[] curvature) {
            this.points = points;
            this.arc = arc;
            this.curvature = curvature;
        }
        public int size() { return points.size(); }
        public double length() { return arc.length == 0 ? 0 : arc[arc.length - 1]; }
    }

    public static Track analyze(List<Point> input) {
        ArrayList<Point> result = new ArrayList<>(input);
        // Two short binomial smoothing passes reject stylus jitter without
        // moving endpoints; the original samples are retained separately.
        for (int pass = 0; pass < 2 && result.size() > 4; pass++) {
            ArrayList<Point> next = new ArrayList<>(result.size());
            next.add(result.get(0));
            for (int i = 1; i + 1 < result.size(); i++) {
                Point a = result.get(i - 1), b = result.get(i), c = result.get(i + 1);
                next.add(new Point((a.x + 2 * b.x + c.x) * 0.25,
                                   (a.y + 2 * b.y + c.y) * 0.25));
            }
            next.add(result.get(result.size() - 1));
            result = next;
        }
        int n = result.size();
        double[] s = new double[n];
        double[] k = new double[n];
        for (int i = 1; i < n; i++) {
            s[i] = s[i - 1] + distance(result.get(i - 1), result.get(i));
        }
        for (int i = 1; i < n - 1; i++) {
            Point p = result.get(i - 1), q = result.get(i), r = result.get(i + 1);
            double ax = q.x - p.x, ay = q.y - p.y;
            double bx = r.x - q.x, by = r.y - q.y;
            double ac = r.x - p.x, bc = r.y - p.y;
            double denom = Math.hypot(ax, ay) * Math.hypot(bx, by) * Math.hypot(ac, bc);
            k[i] = denom > 1e-9 ? -2 * (ax * by - ay * bx) / denom : 0;
        }
        if (n >= 3) {
            k[0] = k[1];
            k[n - 1] = k[n - 2];
        }
        return new Track(result, s, k);
    }

    public static double height(Track track, int anchor, int index) {
        int n = track.size();
        if (n < 2 || anchor < 0 || anchor >= n || index < 0 || index >= n) return 0;
        Point p = track.points.get(Math.max(0, anchor - 1));
        Point q = track.points.get(Math.min(n - 1, anchor + 1));
        double tx = q.x - p.x, ty = q.y - p.y;
        double norm = Math.hypot(tx, ty);
        if (norm < 1e-9) return 0;
        Point o = track.points.get(anchor), at = track.points.get(index);
        // Left unit normal, converted to screen coordinates: (ty,-tx).
        return ((at.x - o.x) * ty - (at.y - o.y) * tx) / norm;
    }

    public static double heightSecondDerivative(Track track, int anchor) {
        if (anchor <= 0 || anchor + 1 >= track.size()) return 0;
        double left = track.arc[anchor] - track.arc[anchor - 1];
        double right = track.arc[anchor + 1] - track.arc[anchor];
        if (left < 1e-9 || right < 1e-9) return 0;
        double hPrev = height(track, anchor, anchor - 1);
        double hNext = height(track, anchor, anchor + 1);
        return 2.0 * (hNext / right + hPrev / left) / (left + right);
    }

    public static int nearest(Track track, double x, double y) {
        int best = 0;
        double bestSq = Double.POSITIVE_INFINITY;
        for (int i = 0; i < track.size(); i++) {
            Point p = track.points.get(i);
            double d = (p.x - x) * (p.x - x) + (p.y - y) * (p.y - y);
            if (d < bestSq) { bestSq = d; best = i; }
        }
        return best;
    }

    public static double distance(Point a, Point b) {
        return Math.hypot(a.x - b.x, a.y - b.y);
    }
}
