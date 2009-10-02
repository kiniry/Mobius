package java.awt.peer;

import java.awt.Adjustable;

public interface ScrollPanePeer extends ContainerPeer {
    
    int getHScrollbarHeight();
    
    int getVScrollbarWidth();
    
    void setScrollPosition(int x, int y);
    
    void childResized(int w, int h);
    
    void setUnitIncrement(Adjustable adj, int u);
    
    void setValue(Adjustable adj, int v);
}
