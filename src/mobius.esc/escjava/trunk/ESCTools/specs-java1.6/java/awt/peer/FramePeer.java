package java.awt.peer;

import java.awt.*;

public interface FramePeer extends WindowPeer {
    
    void setTitle(String title);
    
    void setIconImage(Image im);
    
    void setMenuBar(MenuBar mb);
    
    void setResizable(boolean resizeable);
    
    void setState(int state);
    
    int getState();
    
    void setMaximizedBounds(Rectangle bounds);
    
    void setBoundsPrivate(int x, int y, int width, int height);
}
