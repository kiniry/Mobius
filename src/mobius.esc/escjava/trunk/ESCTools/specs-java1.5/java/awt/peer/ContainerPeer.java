package java.awt.peer;

import java.awt.*;

public interface ContainerPeer extends ComponentPeer {
    
    Insets getInsets();
    
    void beginValidate();
    
    void endValidate();
    
    void beginLayout();
    
    void endLayout();
    
    boolean isPaintPending();
    
    void cancelPendingPaint(int x, int y, int w, int h);
    
    void restack();
    
    boolean isRestackSupported();
    
    Insets insets();
}
