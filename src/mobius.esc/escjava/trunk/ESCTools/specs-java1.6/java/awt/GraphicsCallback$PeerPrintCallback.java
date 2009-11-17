package java.awt;

import java.awt.peer.LightweightPeer;

final class GraphicsCallback$PeerPrintCallback extends GraphicsCallback {
    private static GraphicsCallback$PeerPrintCallback instance = new GraphicsCallback$PeerPrintCallback();
    
    private GraphicsCallback$PeerPrintCallback() {
        
    }
    
    public void run(Component comp, Graphics cg) {
        comp.validate();
        if (comp.peer instanceof LightweightPeer) {
            comp.lightweightPrint(cg);
        } else {
            comp.peer.print(cg);
        }
    }
    
    static GraphicsCallback$PeerPrintCallback getInstance() {
        return instance;
    }
}
