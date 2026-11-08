import com.primitive.neonorbit.OrbitPhysics;

public final class OrbitPhysicsTest {
    private static void check(boolean ok, String description) {
        if (!ok) throw new AssertionError(description);
    }
    public static void main(String[] args) {
        OrbitPhysics.Body b = new OrbitPhysics.Body(100, 100, 10);
        for (int i = 0; i < 30; i++) OrbitPhysics.stepPlayer(b, 250, 100, true,
                1f / 60f, 0, 0, 400, 400);
        check(b.x > 100, "touch attracts the player");
        check(Math.abs(b.y - 100) < .01, "symmetric axis stays invariant");
        for (int i = 0; i < 400; i++) OrbitPhysics.stepPlayer(b, 3000, 3000, true,
                1f / 60f, 0, 0, 400, 400);
        check(b.x >= 10 && b.x <= 390 && b.y >= 10 && b.y <= 390,
                "ball remains inside bounds");
        OrbitPhysics.Body a = new OrbitPhysics.Body(0, 0, 10);
        OrbitPhysics.Body c = new OrbitPhysics.Body(19, 0, 10);
        check(OrbitPhysics.touching(a, c), "overlap");
        c.x = 21;
        check(!OrbitPhysics.touching(a, c), "disjoint");
        check(OrbitPhysics.nextCombo(7, 3.9f) == 8, "combo cap");
        check(OrbitPhysics.nextCombo(8, 5f) == 1, "combo reset");
        check(OrbitPhysics.points(100, 4, true) == 800, "fever multiplier");
        System.out.println("PASS: OrbitPhysics (steering, bounds, collisions, combo, fever)");
    }
}
