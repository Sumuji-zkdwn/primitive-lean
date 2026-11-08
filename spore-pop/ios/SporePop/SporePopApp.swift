import SwiftUI

@main
struct SporePopApp: App {
    var body: some Scene {
        WindowGroup {
            SporeGameView()
                .ignoresSafeArea()
                .statusBarHidden(true)
                .persistentSystemOverlays(.hidden)
        }
    }
}
