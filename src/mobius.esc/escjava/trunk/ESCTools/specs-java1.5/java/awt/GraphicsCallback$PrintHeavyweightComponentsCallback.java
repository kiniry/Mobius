package java.awt;

import java.awt.peer.LightweightPeer;

final class GraphicsCallback$PrintHeavyweightComponentsCallback extends GraphicsCallback {
    private static GraphicsCallback$PrintHeavyweightComponentsCallback instance = new GraphicsCallback$PrintHeavyweightComponentsCallback();
    
    private GraphicsCallback$PrintHeavyweightComponentsCallback() {
        
    }
    
    public void run(Component comp, Graphics cg) {
        if (comp.peer instanceof LightweightPeer) {
            comp.printHeavyweightComponents(cg);
        } else {
            comp.printAll(cg);
        }
    }
    
    static GraphicsCallback$PrintHeavyweightComponentsCallback getInstance() {
        return instance;
    }
}
