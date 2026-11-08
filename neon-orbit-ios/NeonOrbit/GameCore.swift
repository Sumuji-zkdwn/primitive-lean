import Foundation

/// Platform-independent rules shared with the Android version.
/// Coordinates are in logical screen points, with (0,0) at the top-left.
struct OrbitBody {
    var x: Double
    var y: Double
    var vx: Double = 0
    var vy: Double = 0
    var radius: Double
}

enum OrbitRules {
    static func clamp(_ v: Double, _ a: Double, _ b: Double) -> Double {
        min(b, max(a, v))
    }

    static func distance(_ a: OrbitBody, _ b: OrbitBody) -> Double {
        hypot(a.x - b.x, a.y - b.y)
    }

    static func touching(_ a: OrbitBody, _ b: OrbitBody) -> Bool {
        let dx = a.x - b.x
        let dy = a.y - b.y
        let rr = a.radius + b.radius
        return dx * dx + dy * dy <= rr * rr
    }

    static func nextCombo(_ old: Int, sinceLastCollect seconds: Double) -> Int {
        seconds <= 4 ? min(8, old + 1) : 1
    }

    static func points(base: Int, combo: Int, fever: Bool) -> Int {
        base * min(8, max(1, combo)) * (fever ? 2 : 1)
    }

    static func stepPlayer(
        _ b: inout OrbitBody,
        targetX: Double, targetY: Double, holding: Bool,
        dt inputDt: Double, left: Double, top: Double, right: Double, bottom: Double
    ) {
        guard inputDt > 0 else { return }
        let dt = min(inputDt, 0.04)
        if holding {
            b.vx += (targetX - b.x) * 8.2 * dt
            b.vy += (targetY - b.y) * 8.2 * dt
        }
        let drag = pow(holding ? 0.987 : 0.994, dt * 60)
        b.vx *= drag
        b.vy *= drag
        let speed = hypot(b.vx, b.vy)
        if speed > 890 {
            b.vx *= 890 / speed
            b.vy *= 890 / speed
        }
        b.x += b.vx * dt
        b.y += b.vy * dt
        if b.x - b.radius < left {
            b.x = left + b.radius
            b.vx = abs(b.vx) * 0.48
        }
        if b.x + b.radius > right {
            b.x = right - b.radius
            b.vx = -abs(b.vx) * 0.48
        }
        if b.y - b.radius < top {
            b.y = top + b.radius
            b.vy = abs(b.vy) * 0.48
        }
        if b.y + b.radius > bottom {
            b.y = bottom - b.radius
            b.vy = -abs(b.vy) * 0.48
        }
    }
}
