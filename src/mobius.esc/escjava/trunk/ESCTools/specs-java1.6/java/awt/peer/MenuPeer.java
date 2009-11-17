package java.awt.peer;

import java.awt.MenuItem;

public interface MenuPeer extends MenuItemPeer {
    
    void addSeparator();
    
    void addItem(MenuItem item);
    
    void delItem(int index);
}
