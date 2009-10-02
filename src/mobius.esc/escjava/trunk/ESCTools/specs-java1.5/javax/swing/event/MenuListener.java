package javax.swing.event;

import java.util.EventListener;

public interface MenuListener extends EventListener {
    
    void menuSelected(MenuEvent e);
    
    void menuDeselected(MenuEvent e);
    
    void menuCanceled(MenuEvent e);
}
