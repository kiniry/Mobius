package java.awt.peer;

import java.awt.Menu;

public interface MenuBarPeer extends MenuComponentPeer {
    
    void addMenu(Menu m);
    
    void delMenu(int index);
    
    void addHelpMenu(Menu m);
}
