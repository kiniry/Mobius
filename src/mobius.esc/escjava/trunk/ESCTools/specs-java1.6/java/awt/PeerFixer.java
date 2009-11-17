package java.awt;

import java.awt.peer.ScrollPanePeer;
import java.awt.event.*;
import javax.accessibility.*;

class PeerFixer implements AdjustmentListener, java.io.Serializable {
    
    PeerFixer(ScrollPane scroller) {
        
        this.scroller = scroller;
    }
    
    public void adjustmentValueChanged(AdjustmentEvent e) {
        Adjustable adj = e.getAdjustable();
        int value = e.getValue();
        ScrollPanePeer peer = (ScrollPanePeer)(ScrollPanePeer)scroller.peer;
        if (peer != null) {
            peer.setValue(adj, value);
        }
        Component c = scroller.getComponent(0);
        switch (adj.getOrientation()) {
        case Adjustable.VERTICAL: 
            c.move(c.getLocation().x, -(value));
            break;
        
        case Adjustable.HORIZONTAL: 
            c.move(-(value), c.getLocation().y);
            break;
        
        default: 
            throw new IllegalArgumentException("Illegal adjustable orientation");
        
        }
    }
    private ScrollPane scroller;
}
