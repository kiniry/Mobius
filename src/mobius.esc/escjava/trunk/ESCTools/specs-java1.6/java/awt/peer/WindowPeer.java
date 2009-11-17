package java.awt.peer;

import java.awt.*;

public interface WindowPeer extends ContainerPeer {
    
    void toFront();
    
    void toBack();
    
    void updateAlwaysOnTop();
    
    void updateFocusableWindowState();
    
    boolean requestWindowFocus();
}
