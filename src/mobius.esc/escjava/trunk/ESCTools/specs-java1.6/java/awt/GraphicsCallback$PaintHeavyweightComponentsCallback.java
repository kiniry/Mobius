package java.awt;

import java.awt.peer.LightweightPeer;

final class GraphicsCallback$PaintHeavyweightComponentsCallback extends GraphicsCallback {
    private static GraphicsCallback$PaintHeavyweightComponentsCallback instance = new GraphicsCallback$PaintHeavyweightComponentsCallback();
    
    private GraphicsCallback$PaintHeavyweightComponentsCallback() {
        
    }
    
    public void run(Component comp, Graphics cg) {
        if (comp.peer instanceof LightweightPeer) {
            comp.paintHeavyweightComponents(cg);
        } else {
            comp.paintAll(cg);
        }
    }
    
    static GraphicsCallback$PaintHeavyweightComponentsCallback getInstance() {
        return instance;
    }
}
