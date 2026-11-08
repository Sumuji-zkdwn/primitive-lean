import com.primitive.curvelab.Geometry;
import java.util.ArrayList;

public final class GeometryTest {
    static void near(String name, double expected, double actual, double tolerance) {
        if (!Double.isFinite(actual) || Math.abs(expected - actual) > tolerance) {
            throw new AssertionError(name + " expected " + expected + " actual " + actual);
        }
        System.out.printf("PASS %-32s % .7f%n", name, actual);
    }
    static ArrayList<Geometry.Point> sample(double radius, boolean reverse) {
        ArrayList<Geometry.Point> list = new ArrayList<>();
        int n = 101;
        for (int i = 0; i < n; i++) {
            double theta = -0.70 + (reverse ? n - 1 - i : i) * (1.40 / (n - 1));
            // Circle CCW in mathematical coordinates (screen y is flipped).
            list.add(new Geometry.Point(radius * Math.cos(theta), -radius * Math.sin(theta)));
        }
        return list;
    }
    public static void main(String[] args) {
        ArrayList<Geometry.Point> line = new ArrayList<>();
        for (int i = 0; i < 50; i++) line.add(new Geometry.Point(5 * i, 2 * i));
        Geometry.Track straight = Geometry.analyze(line);
        near("straight curvature", 0, straight.curvature[25], 1e-9);
        near("straight second derivative", 0, Geometry.heightSecondDerivative(straight, 25), 1e-9);
        near("anchor has zero height", 0, Geometry.height(straight, 25, 25), 1e-9);

        Geometry.Track circle = Geometry.analyze(sample(120, false));
        near("circle curvature", 1.0 / 120, circle.curvature[50], 1e-4);
        near("height h'' equals curvature", circle.curvature[50],
             Geometry.heightSecondDerivative(circle, 50), 1e-5);
        Geometry.Track reversed = Geometry.analyze(sample(120, true));
        near("reverse flips signed curvature", -circle.curvature[50], reversed.curvature[50], 1e-6);

        ArrayList<Geometry.Point> shifted = new ArrayList<>();
        for (Geometry.Point p : sample(120, false)) {
            shifted.add(new Geometry.Point(p.x + 370, p.y - 90));
        }
        Geometry.Track moved = Geometry.analyze(shifted);
        near("translation invariance", circle.curvature[50], moved.curvature[50], 1e-8);
        near("height translation invariance", Geometry.height(circle, 50, 66),
             Geometry.height(moved, 50, 66), 1e-8);
        System.out.println("All geometry tests passed.");
    }
}
