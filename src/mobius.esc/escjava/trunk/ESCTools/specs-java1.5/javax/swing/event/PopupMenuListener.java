package javax.swing.event;

import java.util.EventListener;

public interface PopupMenuListener extends EventListener {
    
    void popupMenuWillBecomeVisible(PopupMenuEvent e);
    
    void popupMenuWillBecomeInvisible(PopupMenuEvent e);
    
    void popupMenuCanceled(PopupMenuEvent e);
}
