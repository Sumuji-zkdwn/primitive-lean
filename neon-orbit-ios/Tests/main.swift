import Foundation
func check(_ condition: @autoclosure () -> Bool, _ message: String) {
    if !condition() { fputs("FAIL: \(message)\n", stderr); exit(1) }
}
var p = OrbitBody(x: 150, y: 320, radius: 12)
for _ in 0..<30 {
    OrbitRules.stepPlayer(&p, targetX: 270, targetY: 320, holding: true,
                          dt: 1.0 / 60, left: 17, top: 155, right: 375, bottom: 700)
}
check(p.x > 150 && p.vx > 0, "gravity moves toward finger")
check(abs(p.y - 320) < 0.0001, "no unwanted vertical drift")
var wall = OrbitBody(x: 30, y: 300, vx: -300, vy: 0, radius: 12)
OrbitRules.stepPlayer(&wall, targetX: 0, targetY: 0, holding: false,
                      dt: 0.035, left: 17, top: 155, right: 375, bottom: 700)
check(wall.x >= 29 && wall.vx > 0, "left wall rebounds")
check(OrbitRules.touching(OrbitBody(x: 0, y: 0, radius: 12), OrbitBody(x: 31, y: 0, radius: 19)), "touch inclusive")
check(!OrbitRules.touching(OrbitBody(x: 0, y: 0, radius: 12), OrbitBody(x: 31.01, y: 0, radius: 19)), "touch exclusive")
check(OrbitRules.nextCombo(7, sinceLastCollect: 3.9) == 8, "combo max")
check(OrbitRules.nextCombo(8, sinceLastCollect: 4.01) == 1, "combo reset")
check(OrbitRules.points(base: 100, combo: 4, fever: true) == 800, "fever doubles")
check(OrbitRules.points(base: 150, combo: 99, fever: false) == 1200, "combo capped")
print("PASS: NEON ORBIT iOS physics, collision, combo and fever")
