import SwiftUI
import SpriteKit

@main
struct NeonOrbitApp: App {
    var body: some Scene {
        WindowGroup {
            OrbitGameView()
                .ignoresSafeArea()
                .statusBarHidden(true)
                .persistentSystemOverlays(.hidden)
        }
    }
}

struct OrbitGameView: UIViewRepresentable {
    func makeUIView(context: Context) -> SKView {
        let view = SKView(frame: UIScreen.main.bounds)
        view.ignoresSiblingOrder = true
        view.preferredFramesPerSecond = 60
        view.isMultipleTouchEnabled = false
        let scene = GameScene(size: UIScreen.main.bounds.size)
        scene.scaleMode = .resizeFill
        view.presentScene(scene)
        return view
    }

    func updateUIView(_ view: SKView, context: Context) { }
}
