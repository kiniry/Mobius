package java.awt;

import java.awt.peer.LightweightPeer;

final class GraphicsCallback$PeerPaintCallback extends GraphicsCallback {
    private static GraphicsCallback$PeerPaintCallback instance = new GraphicsCallback$PeerPaintCallback();
    
    private GraphicsCallback$PeerPaintCallback() {
        
    }
    
    public void run(Component comp, Graphics cg) {
        comp.validate();
        if (comp.peer instanceof LightweightPeer) {
            comp.lightweightPaint(cg);
        } else {
            comp.peer.paint(cg);
        }
    }
    
    static GraphicsCallback$PeerPaintCallback getInstance() {
        return instance;
    }
}
