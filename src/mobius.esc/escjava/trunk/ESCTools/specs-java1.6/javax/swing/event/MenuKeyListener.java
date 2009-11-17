package javax.swing.event;

import java.util.EventListener;

public interface MenuKeyListener extends EventListener {
    
    void menuKeyTyped(MenuKeyEvent e);
    
    void menuKeyPressed(MenuKeyEvent e);
    
    void menuKeyReleased(MenuKeyEvent e);
}
