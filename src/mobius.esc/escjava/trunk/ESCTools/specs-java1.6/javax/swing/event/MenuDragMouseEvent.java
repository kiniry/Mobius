package javax.swing.event;

import javax.swing.MenuElement;
import javax.swing.MenuSelectionManager;
import java.awt.event.MouseEvent;
import java.awt.Component;

public class MenuDragMouseEvent extends MouseEvent {
    private MenuElement[] path;
    private MenuSelectionManager manager;
    
    public MenuDragMouseEvent(Component source, int id, long when, int modifiers, int x, int y, int clickCount, boolean popupTrigger, MenuElement[] p, MenuSelectionManager m) {
        super(source, id, when, modifiers, x, y, clickCount, popupTrigger);
        path = p;
        manager = m;
    }
    
    public MenuElement[] getPath() {
        return path;
    }
    
    public MenuSelectionManager getMenuSelectionManager() {
        return manager;
    }
}
