import UIKit
import SpriteKit
import AVFoundation

/// Native SpriteKit rendering and touch input; physics and scoring in GameCore.swift.
final class GameScene: SKScene {
    private enum Mode { case ready, play, pause, finish }
    private enum PrizeKind { case gold, clock, fever }
    private struct Prize { var x: Double; var y: Double; let kind: PrizeKind }
    private struct Mine { var body: OrbitBody; var angle: Double; let spin: Double }
    private struct Dust {
        var x: Double; var y: Double; var vx: Double; var vy: Double
        var remaining: Double; let total: Double; let r: Double; let color: UIColor
    }
    private struct Spark { let x: Double; let y: Double; let r: Double; let phase: Double }
    private struct Trace { let x: Double; let y: Double }

    private enum Palette {
        static let dark = UIColor(red: 5/255, green: 9/255, blue: 24/255, alpha: 1)
        static let navy = UIColor(red: 11/255, green: 20/255, blue: 46/255, alpha: 1)
        static let blue = UIColor(red: 88/255, green: 236/255, blue: 1, alpha: 1)
        static let pink = UIColor(red: 1, green: 72/255, blue: 152/255, alpha: 1)
        static let red = UIColor(red: 1, green: 83/255, blue: 106/255, alpha: 1)
        static let gold = UIColor(red: 1, green: 210/255, blue: 101/255, alpha: 1)
        static let lime = UIColor(red: 142/255, green: 252/255, blue: 181/255, alpha: 1)
        static let white = UIColor(red: 239/255, green: 245/255, blue: 1, alpha: 1)
        static let muted = UIColor(red: 135/255, green: 154/255, blue: 194/255, alpha: 1)
    }

    private let backgroundLayer = SKNode()
    private let playLayer = SKNode()
    private let hudLayer = SKNode()
    private let overlayLayer = SKNode()
    private var mode: Mode = .ready
    private var player = OrbitBody(x: 180, y: 400, radius: 12)
    private var prize: Prize?
    private var mines: [Mine] = []
    private var particles: [Dust] = []
    private var trail: [Trace] = []
    private var stars: [Spark] = []
    private var audioPlayers: [AVAudioPlayer] = []
    private var lastFrame: TimeInterval = 0
    private var top = 165.0
    private var bottom = 650.0
    private var timeLeft = 60.0
    private var playTime = 0.0
    private var lastCollect = -100.0
    private var fever = 0.0
    private var invincible = 0.0
    private var shake = 0.0
    private var flash = 0.0
    private var ambient = 0.0
    private var score = 0
    private var lives = 3
    private var combo = 0
    private var collected = 0
    private var best = UserDefaults.standard.integer(forKey: "neon_orbit_best")
    private var sound = UserDefaults.standard.object(forKey: "neon_orbit_sound") as? Bool ?? true
    private var holding = false
    private var targetX = 0.0
    private var targetY = 0.0

    private var w: Double { Double(size.width) }
    private var h: Double { Double(size.height) }
    private func random(_ a: Double, _ b: Double) -> Double { Double.random(in: a...max(a, b)) }
    private func clamp(_ v: Double, _ a: Double, _ b: Double) -> Double { OrbitRules.clamp(v, a, b) }
    private func p(_ x: Double, _ y: Double) -> CGPoint { CGPoint(x: x, y: h - y) }

    override func didMove(to view: SKView) {
        backgroundColor = Palette.dark
        addChild(backgroundLayer)
        addChild(playLayer)
        addChild(hudLayer)
        addChild(overlayLayer)
        view.isMultipleTouchEnabled = false
        buildBackground()
        player = OrbitBody(x: w * 0.5, y: (top + bottom) * 0.5, radius: 12)
        targetX = player.x
        targetY = player.y
        prize = Prize(x: w * 0.73, y: top + (bottom - top) * 0.3, kind: .gold)
        NotificationCenter.default.addObserver(self, selector: #selector(pauseForInterruption),
                                               name: UIApplication.willResignActiveNotification, object: nil)
    }

    deinit { NotificationCenter.default.removeObserver(self) }

    override func didChangeSize(_ oldSize: CGSize) {
        super.didChangeSize(oldSize)
        guard size.width > 0, size.height > 0 else { return }
        buildBackground()
        player.x = clamp(player.x, 28, max(28, w - 28))
        player.y = clamp(player.y, top + 22, max(top + 22, bottom - 22))
    }

    @objc private func pauseForInterruption() {
        if mode == .play { mode = .pause; holding = false }
        lastFrame = 0
    }

    private func buildBackground() {
        backgroundLayer.removeAllChildren()
        let safeTop = Double(view?.safeAreaInsets.top ?? 0)
        let safeBottom = Double(view?.safeAreaInsets.bottom ?? 0)
        top = safeTop + 148
        bottom = max(top + 160, h - safeBottom - 100)
        // Static vertical gradient, created locally. No image assets, network or dependencies.
        let renderer = UIGraphicsImageRenderer(size: CGSize(width: max(1, size.width), height: max(1, size.height)))
        let image = renderer.image { context in
            let colors = [Palette.navy.cgColor, Palette.dark.cgColor] as CFArray
            if let gradient = CGGradient(colorsSpace: CGColorSpaceCreateDeviceRGB(), colors: colors, locations: [0, 1]) {
                context.cgContext.drawLinearGradient(gradient, start: .zero,
                                                     end: CGPoint(x: size.width * 0.7, y: size.height), options: [])
            }
        }
        let bg = SKSpriteNode(texture: SKTexture(image: image))
        bg.size = size
        bg.position = CGPoint(x: size.width / 2, y: size.height / 2)
        bg.zPosition = -10
        backgroundLayer.addChild(bg)
        let grid = CGMutablePath()
        var x = 0.0
        while x <= w { grid.move(to: p(x, 0)); grid.addLine(to: p(x, h)); x += 45 }
        var y = 0.0
        while y <= h { grid.move(to: p(0, y)); grid.addLine(to: p(w, y)); y += 45 }
        let gridNode = SKShapeNode(path: grid)
        gridNode.strokeColor = UIColor(red: 55/255, green: 88/255, blue: 137/255, alpha: 0.18)
        gridNode.lineWidth = 0.7
        backgroundLayer.addChild(gridNode)
        backgroundLayer.addChild(line(19, top, w - 19, top, Palette.blue, 0.23, 1))
        backgroundLayer.addChild(line(19, bottom, w - 19, bottom, Palette.blue, 0.23, 1))
        stars = (0..<75).map { _ in Spark(x: random(0, w), y: random(0, h), r: random(0.4, 1.8), phase: random(0, .pi * 2)) }
        for s in stars { backgroundLayer.addChild(circle(s.x, s.y, s.r, Palette.white, 0.22)) }
    }

    private func circle(_ x: Double, _ y: Double, _ r: Double, _ color: UIColor, _ opacity: CGFloat = 1) -> SKNode {
        let shape = SKShapeNode(circleOfRadius: CGFloat(max(0.01, r)))
        shape.position = p(x, y)
        shape.fillColor = color
        shape.strokeColor = .clear
        shape.alpha = opacity
        return shape
    }

    private func ring(_ x: Double, _ y: Double, _ r: Double, _ color: UIColor,
                      _ opacity: CGFloat = 1, _ width: Double = 1.3) -> SKNode {
        let shape = SKShapeNode(circleOfRadius: CGFloat(max(0.01, r)))
        shape.position = p(x, y)
        shape.fillColor = .clear
        shape.strokeColor = color
        shape.lineWidth = CGFloat(width)
        shape.alpha = opacity
        return shape
    }

    private func line(_ x1: Double, _ y1: Double, _ x2: Double, _ y2: Double,
                      _ color: UIColor, _ opacity: CGFloat = 1, _ width: Double = 1) -> SKNode {
        let path = CGMutablePath()
        path.move(to: p(x1, y1))
        path.addLine(to: p(x2, y2))
        let node = SKShapeNode(path: path)
        node.strokeColor = color
        node.lineWidth = CGFloat(width)
        node.alpha = opacity
        return node
    }

    private func panel(_ x: Double, _ y: Double, _ width: Double, _ height: Double,
                       _ color: UIColor, _ opacity: CGFloat = 1, corner: Double = 0) -> SKNode {
        let node = SKShapeNode(rectOf: CGSize(width: width, height: height), cornerRadius: CGFloat(corner))
        node.position = p(x, y)
        node.fillColor = color
        node.strokeColor = .clear
        node.alpha = opacity
        return node
    }

    private func text(_ string: String, _ x: Double, _ y: Double, _ size: Double,
                      _ color: UIColor, centered: Bool = true, heavy: Bool = false) -> SKNode {
        let label = SKLabelNode(fontNamed: heavy ? "AvenirNextCondensed-Heavy" : "AvenirNext-Medium")
        label.text = string
        label.fontSize = CGFloat(size)
        label.fontColor = color
        label.position = p(x, y)
        label.verticalAlignmentMode = .center
        label.horizontalAlignmentMode = centered ? .center : .left
        return label
    }

    private func star(_ x: Double, _ y: Double, _ radius: Double, _ color: UIColor, _ rotation: Double) -> SKNode {
        let path = CGMutablePath()
        for i in 0..<10 {
            let a = -.pi / 2 + Double(i) * .pi / 5 + rotation
            let r = i % 2 == 0 ? radius : radius * 0.47
            let point = p(x + cos(a) * r, y + sin(a) * r)
            if i == 0 { path.move(to: point) } else { path.addLine(to: point) }
        }
        path.closeSubpath()
        let node = SKShapeNode(path: path)
        node.fillColor = color
        node.strokeColor = .clear
        return node
    }

    private func burst(_ x: Double, _ y: Double, _ color: UIColor, _ n: Int = 28) {
        for _ in 0..<n {
            let a = random(0, .pi * 2)
            let speed = random(60, 330)
            let duration = random(0.3, 0.84)
            particles.append(Dust(x: x, y: y, vx: cos(a) * speed, vy: sin(a) * speed,
                                  remaining: duration, total: duration, r: random(1.3, 3.8), color: color))
        }
        if particles.count > 260 { particles.removeFirst(particles.count - 260) }
    }

    private func spawnPrize() {
        let type: PrizeKind = random(0, 1) < 0.12 ? .clock : (random(0, 1) < 0.17 ? .fever : .gold)
        var x = w * 0.5
        var y = (top + bottom) * 0.5
        for _ in 0..<100 {
            x = random(46, w - 46)
            y = random(top + 42, bottom - 42)
            if hypot(x - player.x, y - player.y) < 120 { continue }
            if mines.contains(where: { hypot(x - $0.body.x, y - $0.body.y) < 66 }) { continue }
            break
        }
        prize = Prize(x: x, y: y, kind: type)
    }

    private func addMine() {
        guard mines.count < 7 else { return }
        let r = random(14, 19)
        var x = w * 0.25
        var y = top + 60
        for _ in 0..<90 {
            x = random(r + 25, w - r - 25)
            y = random(top + 30, bottom - 30)
            if hypot(x - player.x, y - player.y) < 130 { continue }
            if let p = prize, hypot(x - p.x, y - p.y) < 90 { continue }
            if mines.contains(where: { hypot(x - $0.body.x, y - $0.body.y) < 60 }) { continue }
            break
        }
        let a = random(0, .pi * 2)
        let speed = random(48, 90)
        mines.append(Mine(body: OrbitBody(x: x, y: y, vx: cos(a) * speed, vy: sin(a) * speed, radius: r),
                          angle: random(0, .pi * 2), spin: Bool.random() ? 1 : -1))
    }

    private func soundEffect(_ frequency: Double, duration: Double = 0.09) {
        guard sound else { return }
        // Short generated PCM sound. No bundled or network audio, no copyright concerns.
        let rate = 22050
        let count = Int(Double(rate) * duration)
        var data = Data()
        func appendLE<T: FixedWidthInteger>(_ value: T) {
            var v = value.littleEndian
            withUnsafeBytes(of: &v) { data.append(contentsOf: $0) }
        }
        data.append(contentsOf: "RIFF".utf8)
        appendLE(UInt32(36 + count * 2))
        data.append(contentsOf: "WAVEfmt ".utf8)
        appendLE(UInt32(16))
        appendLE(UInt16(1))
        appendLE(UInt16(1))
        appendLE(UInt32(rate))
        appendLE(UInt32(rate * 2))
        appendLE(UInt16(2))
        appendLE(UInt16(16))
        data.append(contentsOf: "data".utf8)
        appendLE(UInt32(count * 2))
        for i in 0..<count {
            let t = Double(i) / Double(rate)
            let envelope = pow(max(0, 1 - Double(i) / Double(count)), 2.0)
            let sample = Int16(sin(t * frequency * .pi * 2) * envelope * 9500)
            appendLE(sample.bitPattern)
        }
        if let player = try? AVAudioPlayer(data: data) {
            player.volume = 0.3
            player.prepareToPlay()
            player.play()
            audioPlayers.append(player)
        }
    }

    private func startGame() {
        mode = .play
        score = 0; lives = 3; collected = 0; combo = 0
        timeLeft = 60; playTime = 0; lastCollect = -100
        fever = 0; invincible = 0; flash = 0; shake = 0; holding = false
        mines.removeAll(); particles.removeAll(); trail.removeAll()
        player = OrbitBody(x: w * 0.5, y: top + (bottom - top) * 0.58, radius: 12)
        targetX = player.x; targetY = player.y
        spawnPrize(); addMine(); addMine()
        soundEffect(660)
    }

    private func finishGame() {
        guard mode == .play else { return }
        mode = .finish
        holding = false
        best = max(best, score)
        UserDefaults.standard.set(best, forKey: "neon_orbit_best")
        burst(player.x, player.y, Palette.blue, 36)
        soundEffect(180, duration: 0.22)
    }

    private func collect() {
        guard let prize else { return }
        combo = OrbitRules.nextCombo(combo, sinceLastCollect: playTime - lastCollect)
        lastCollect = playTime
        collected += 1
        if prize.kind == .clock { timeLeft = min(90, timeLeft + 5) }
        if prize.kind == .fever { fever = max(fever, 5) }
        score += OrbitRules.points(base: prize.kind == .gold ? 100 : 150, combo: combo, fever: fever > 0)
        best = max(best, score)
        let color = prize.kind == .clock ? Palette.lime : prize.kind == .fever ? Palette.pink : Palette.gold
        burst(prize.x, prize.y, color)
        flash = 0.12
        if collected % 5 == 0 { addMine() }
        soundEffect(430 + Double(combo) * 75)
        UIImpactFeedbackGenerator(style: .light).impactOccurred()
        spawnPrize()
    }

    private func hit(_ mine: Mine) {
        guard invincible <= 0 && fever <= 0 else { return }
        lives -= 1
        combo = 0
        invincible = 1.65
        shake = 0.25
        flash = 0.22
        burst(player.x, player.y, Palette.red, 31)
        player.vx = -player.vx * 0.5 + (player.x - mine.body.x) * 2
        player.vy = -player.vy * 0.5 + (player.y - mine.body.y) * 2
        soundEffect(165, duration: 0.17)
        UINotificationFeedbackGenerator().notificationOccurred(.error)
        if lives <= 0 { finishGame() }
    }

    private func step(_ dt: Double) {
        ambient += dt
        flash = max(0, flash - dt)
        shake = max(0, shake - dt)
        for i in particles.indices.reversed() {
            particles[i].x += particles[i].vx * dt
            particles[i].y += particles[i].vy * dt
            particles[i].vx *= pow(0.982, dt * 60)
            particles[i].vy *= pow(0.982, dt * 60)
            particles[i].remaining -= dt
            if particles[i].remaining <= 0 { particles.remove(at: i) }
        }
        guard mode == .play else { return }
        playTime += dt
        timeLeft -= dt
        fever = max(0, fever - dt)
        invincible = max(0, invincible - dt)
        if timeLeft <= 0 { timeLeft = 0; finishGame(); return }
        OrbitRules.stepPlayer(&player, targetX: targetX, targetY: targetY, holding: holding,
                              dt: dt, left: 17, top: top + 5, right: w - 17, bottom: bottom - 5)
        trail.append(Trace(x: player.x, y: player.y))
        if trail.count > 26 { trail.removeFirst() }
        for i in mines.indices {
            mines[i].body.x += mines[i].body.vx * dt
            mines[i].body.y += mines[i].body.vy * dt
            let r = mines[i].body.radius
            if mines[i].body.x - r < 15 { mines[i].body.x = 15 + r; mines[i].body.vx = abs(mines[i].body.vx) }
            if mines[i].body.x + r > w - 15 { mines[i].body.x = w - 15 - r; mines[i].body.vx = -abs(mines[i].body.vx) }
            if mines[i].body.y - r < top + 4 { mines[i].body.y = top + 4 + r; mines[i].body.vy = abs(mines[i].body.vy) }
            if mines[i].body.y + r > bottom - 4 { mines[i].body.y = bottom - 4 - r; mines[i].body.vy = -abs(mines[i].body.vy) }
            mines[i].angle += mines[i].spin * dt
        }
        if let prize {
            let token = OrbitBody(x: prize.x, y: prize.y, radius: 19)
            if OrbitRules.touching(player, token) { collect() }
        }
        if let mine = mines.first(where: { OrbitRules.touching(player, $0.body) }) { hit(mine) }
    }

    override func update(_ currentTime: TimeInterval) {
        let dt = lastFrame == 0 ? 0 : clamp(currentTime - lastFrame, 0, 0.035)
        lastFrame = currentTime
        step(dt)
        render()
        if !audioPlayers.isEmpty { audioPlayers.removeAll(where: { !$0.isPlaying }) }
    }

    private func render() {
        playLayer.removeAllChildren()
        hudLayer.removeAllChildren()
        overlayLayer.removeAllChildren()
        if fever > 0 && mode == .play { playLayer.addChild(panel(w / 2, (top + bottom) / 2, w, bottom - top, Palette.pink, 0.035)) }
        if holding && mode == .play {
            let pulse = (ambient * 85).truncatingRemainder(dividingBy: 115)
            for i in 0..<3 {
                let r = 20 + (pulse + Double(i) * 38).truncatingRemainder(dividingBy: 128)
                playLayer.addChild(ring(targetX, targetY, r, Palette.pink, CGFloat(max(0, 0.42 * (1 - (r - 20) / 128))), 1.6))
            }
            playLayer.addChild(line(player.x, player.y, targetX, targetY, Palette.pink, 0.34))
            playLayer.addChild(circle(targetX, targetY, 17, Palette.pink, 0.12))
            playLayer.addChild(ring(targetX, targetY, 13, Palette.pink, 0.75, 1.8))
            playLayer.addChild(ring(targetX, targetY, 4, Palette.white, 0.75))
        }
        for (i, t) in trail.enumerated() {
            let ratio = Double(i + 1) / Double(max(1, trail.count))
            playLayer.addChild(circle(t.x, t.y, (3 + ratio * 13) * 0.6, Palette.blue, CGFloat(ratio * ratio * 0.28)))
        }
        for dust in particles {
            let a = clamp(dust.remaining / dust.total, 0, 1)
            playLayer.addChild(circle(dust.x, dust.y, dust.r * 2.5 * a, dust.color, CGFloat(0.13 * a)))
            playLayer.addChild(circle(dust.x, dust.y, dust.r * max(0.2, a), dust.color, CGFloat(0.9 * a)))
        }
        for mine in mines {
            let b = mine.body
            playLayer.addChild(circle(b.x, b.y, b.radius * 1.9, Palette.red, 0.08))
            playLayer.addChild(ring(b.x, b.y, b.radius * 1.28, Palette.red, 0.54))
            for i in 0..<8 {
                let a = mine.angle + Double(i) * .pi / 4
                playLayer.addChild(line(b.x + cos(a) * b.radius * 0.7, b.y + sin(a) * b.radius * 0.7,
                                        b.x + cos(a) * b.radius * 1.47, b.y + sin(a) * b.radius * 1.47,
                                        Palette.red, 0.74, 3.2))
            }
            playLayer.addChild(circle(b.x, b.y, b.radius * 0.78, Palette.red, 0.9))
            playLayer.addChild(ring(b.x, b.y, b.radius * 0.46, Palette.white, 0.7))
            playLayer.addChild(circle(b.x, b.y, b.radius * 0.15, Palette.dark))
        }
        if let prize {
            let pulse = 0.5 + 0.5 * sin(ambient * 4.3)
            let color = prize.kind == .clock ? Palette.lime : prize.kind == .fever ? Palette.pink : Palette.gold
            playLayer.addChild(circle(prize.x, prize.y, 26 + pulse * 7, color, 0.08))
            playLayer.addChild(ring(prize.x, prize.y, 21 + pulse * 4, color, 0.48))
            playLayer.addChild(star(prize.x, prize.y, 12 + pulse * 1.6, color, ambient * 0.22))
            playLayer.addChild(circle(prize.x, prize.y, 3.7, Palette.white))
            if prize.kind == .clock { playLayer.addChild(text("+5s", prize.x, prize.y + 36, 11, Palette.lime, heavy: true)) }
            if prize.kind == .fever { playLayer.addChild(text("2×", prize.x, prize.y + 36, 11, Palette.pink, heavy: true)) }
        }
        if !(invincible > 0 && Int(ambient * 13) % 2 == 0) {
            let r = player.radius
            let pulse = 0.5 + 0.5 * sin(ambient * 5)
            playLayer.addChild(circle(player.x, player.y, r * 2.8 + pulse * 4, Palette.blue, 0.06))
            playLayer.addChild(circle(player.x, player.y, r * 2, Palette.blue, 0.13))
            playLayer.addChild(ring(player.x, player.y, r * 1.53, Palette.blue, 0.46))
            playLayer.addChild(circle(player.x, player.y, r, Palette.blue))
            playLayer.addChild(circle(player.x - r * 0.2, player.y - r * 0.25, r * 0.42, Palette.white, 0.95))
            if fever > 0 { playLayer.addChild(ring(player.x, player.y, r * 1.95, Palette.pink, 0.87, 2.1)) }
            if invincible > 0 { playLayer.addChild(ring(player.x, player.y, r * 2.15, Palette.gold, 0.82, 1.8)) }
        }
        if flash > 0 { playLayer.addChild(panel(w / 2, (top + bottom) / 2, w, bottom - top, invincible > 0 ? Palette.red : Palette.white, CGFloat(flash * 0.4))) }
        renderHUD()
        if mode != .play { renderOverlay() }
    }

    private func renderHUD() {
        let safeTop = Double(view?.safeAreaInsets.top ?? 0)
        let offset = safeTop + 20
        hudLayer.addChild(panel(w / 2, top / 2, w, top - 8, Palette.dark, 0.85))
        hudLayer.addChild(text("SCORE", 23, offset, 10, Palette.muted, centered: false, heavy: true))
        hudLayer.addChild(text(String(format: "%06d", score), 22, offset + 31, 26, Palette.white, centered: false, heavy: true))
        hudLayer.addChild(text("TIME", w * 0.57, offset, 10, Palette.muted, heavy: true))
        hudLayer.addChild(text(String(format: "%04.1f", timeLeft), w * 0.57, offset + 31, 25,
                               timeLeft < 10 && mode == .play ? Palette.red : Palette.blue, heavy: true))
        hudLayer.addChild(text("BEST  " + String(format: "%06d", best), w - 62, offset, 10, Palette.muted, heavy: true))
        for i in 0..<3 { hudLayer.addChild(circle(28 + Double(i) * 22, offset + 63, 6,
                                                   i < lives ? Palette.red : UIColor(white: 0.18, alpha: 1))) }
        hudLayer.addChild(text("SFX " + (sound ? "ON" : "OFF"), w - 114, offset + 66, 11,
                               sound ? Palette.lime : Palette.muted, heavy: true))
        hudLayer.addChild(text("Ⅱ", w - 31, offset + 66, 25, Palette.white, heavy: true))
        hudLayer.addChild(panel(w / 2, top - 22, w - 36, 3, Palette.muted, 0.28, corner: 1.5))
        let pct = clamp(timeLeft / 60, 0, 1)
        if pct > 0 { hudLayer.addChild(panel(18 + (w - 36) * pct / 2, top - 22,
                                            (w - 36) * pct, 3, fever > 0 ? Palette.pink : Palette.blue, 0.95, corner: 1.5)) }
        let status: String
        let statusColor: UIColor
        if mode == .play && fever > 0 {
            status = String(format: "FEVER ×2   %.1fs", fever); statusColor = Palette.pink
        } else if mode == .play && combo > 1 && playTime - lastCollect < 4 {
            status = "COMBO  ×\(combo)"; statusColor = Palette.gold
        } else {
            status = String(format: "WAVE %02d", collected / 5 + 1); statusColor = Palette.muted
        }
        hudLayer.addChild(text(status, w * 0.5, bottom + 27, 15, statusColor, heavy: true))
        hudLayer.addChild(text("HOLD + DRAG", w * 0.5, h - 44, 12, Palette.blue, heavy: true))
        hudLayer.addChild(text("指の位置に引力を発生させる", w * 0.5, h - 25, 12, Palette.muted))
    }

    private func renderOverlay() {
        overlayLayer.addChild(panel(w / 2, h / 2, w, h, Palette.dark, 0.96))
        let cy = h * 0.32
        let title: String
        let buttonText: String
        switch mode {
        case .ready:
            for i in 0..<4 {
                let a = ambient * (i % 2 == 0 ? 0.58 : -0.48) + Double(i) * .pi / 2
                let r = 49 + Double(i) * 10
                let color = i % 2 == 0 ? Palette.blue : Palette.pink
                overlayLayer.addChild(ring(w / 2, cy - 12, r, color, CGFloat(0.22 + Double(3 - i) * 0.1), 1.8))
                overlayLayer.addChild(circle(w / 2 + cos(a) * r, cy - 12 + sin(a) * r,
                                             Double(4 + i % 2 * 2), color, 0.9))
            }
            overlayLayer.addChild(circle(w / 2, cy - 12, 17, Palette.white, 0.95))
            overlayLayer.addChild(text("NEON", w / 2, h * 0.49, 65, Palette.white, heavy: true))
            overlayLayer.addChild(text("ORBIT", w / 2, h * 0.563, 65, Palette.blue, heavy: true))
            overlayLayer.addChild(text("重力で、星を奪え。", w / 2, h * 0.615, 15, Palette.muted, heavy: true))
            buttonText = "START  ▶"
            overlayLayer.addChild(text("HOLD + DRAG で球を引き寄せよう", w / 2, h * 0.815, 12, Palette.white))
            overlayLayer.addChild(text("星を集めろ。機雷を避けろ。60秒勝負。", w / 2, h * 0.85, 12, Palette.muted))
            overlayLayer.addChild(text("OFFLINE · NO ADS · ONE FINGER", w / 2, h * 0.92, 10, Palette.blue, heavy: true))
        case .pause:
            title = "PAUSED"
            overlayLayer.addChild(text(title, w / 2, h * 0.43, 53, Palette.white, heavy: true))
            overlayLayer.addChild(text("指を休めても、宇宙は逃げない。", w / 2, h * 0.49, 13, Palette.muted))
            buttonText = "RESUME  ▶"
        case .finish:
            title = lives <= 0 ? "GAME OVER" : "TIME UP"
            overlayLayer.addChild(text(title, w / 2, h * 0.315, 49, Palette.white, heavy: true))
            overlayLayer.addChild(text("FINAL SCORE", w / 2, h * 0.4, 12, Palette.muted, heavy: true))
            overlayLayer.addChild(text(String(format: "%06d", score), w / 2, h * 0.485, 62, Palette.gold, heavy: true))
            overlayLayer.addChild(text("BEST  " + String(format: "%06d", best), w / 2, h * 0.548, 17, Palette.blue, heavy: true))
            overlayLayer.addChild(text("STARS COLLECTED  \(collected)", w / 2, h * 0.596, 12, Palette.muted))
            overlayLayer.addChild(text("コンボをつなげて最高得点を更新", w / 2, h * 0.815, 12, Palette.white))
            buttonText = "RETRY  ↻"
        case .play: return
        }
        let buttonY = mode == .pause ? h * 0.59 : mode == .ready ? h * 0.73 : h * 0.70
        overlayLayer.addChild(panel(w / 2, buttonY, w - 84, 58, Palette.blue, 0.19, corner: 18))
        overlayLayer.addChild(panel(w / 2, buttonY, w - 90, 53, Palette.blue, 0.96, corner: 16))
        overlayLayer.addChild(text(buttonText, w / 2, buttonY + 1, 22, Palette.dark, heavy: true))
    }

    override func touchesBegan(_ touches: Set<UITouch>, with event: UIEvent?) {
        guard let touch = touches.first else { return }
        let point = touch.location(in: self)
        let x = Double(point.x)
        let y = h - Double(point.y)
        if mode == .ready || mode == .finish { startGame(); return }
        if mode == .pause { mode = .play; holding = false; lastFrame = 0; return }
        guard mode == .play else { return }
        let offset = Double(view?.safeAreaInsets.top ?? 0) + 20
        if y < offset + 93 && x > w - 66 { mode = .pause; holding = false; return }
        if y < offset + 93 && x > w - 153 {
            sound.toggle()
            UserDefaults.standard.set(sound, forKey: "neon_orbit_sound")
            soundEffect(640)
            return
        }
        holding = true
        targetX = clamp(x, 20, w - 20)
        targetY = clamp(y, top + 20, bottom - 20)
    }

    override func touchesMoved(_ touches: Set<UITouch>, with event: UIEvent?) {
        guard mode == .play && holding, let touch = touches.first else { return }
        let point = touch.location(in: self)
        targetX = clamp(Double(point.x), 20, w - 20)
        targetY = clamp(h - Double(point.y), top + 20, bottom - 20)
    }

    override func touchesEnded(_ touches: Set<UITouch>, with event: UIEvent?) { holding = false }
    override func touchesCancelled(_ touches: Set<UITouch>, with event: UIEvent?) { holding = false }
}
