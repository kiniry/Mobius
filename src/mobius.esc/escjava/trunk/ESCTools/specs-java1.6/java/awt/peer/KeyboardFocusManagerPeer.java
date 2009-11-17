package java.awt.peer;

import java.awt.Component;
import java.awt.Window;

public interface KeyboardFocusManagerPeer {
    
    void setCurrentFocusedWindow(Window win);
    
    Window getCurrentFocusedWindow();
    
    void setCurrentFocusOwner(Component comp);
    
    Component getCurrentFocusOwner();
    
    void clearGlobalFocusOwner(Window activeWindow);
}
