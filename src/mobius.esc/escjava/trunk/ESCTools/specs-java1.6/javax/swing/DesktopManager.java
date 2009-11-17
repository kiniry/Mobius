package javax.swing;

public interface DesktopManager {
    
    void openFrame(JInternalFrame f);
    
    void closeFrame(JInternalFrame f);
    
    void maximizeFrame(JInternalFrame f);
    
    void minimizeFrame(JInternalFrame f);
    
    void iconifyFrame(JInternalFrame f);
    
    void deiconifyFrame(JInternalFrame f);
    
    void activateFrame(JInternalFrame f);
    
    void deactivateFrame(JInternalFrame f);
    
    void beginDraggingFrame(JComponent f);
    
    void dragFrame(JComponent f, int newX, int newY);
    
    void endDraggingFrame(JComponent f);
    
    void beginResizingFrame(JComponent f, int direction);
    
    void resizeFrame(JComponent f, int newX, int newY, int newWidth, int newHeight);
    
    void endResizingFrame(JComponent f);
    
    void setBoundsForFrame(JComponent f, int newX, int newY, int newWidth, int newHeight);
}
