package java.awt.peer;

public interface MenuItemPeer extends MenuComponentPeer {
    
    void setLabel(String label);
    
    void setEnabled(boolean b);
    
    void enable();
    
    void disable();
}
