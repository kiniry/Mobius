package javax.swing.event;

import javax.swing.MenuElement;
import javax.swing.MenuSelectionManager;
import java.awt.event.KeyEvent;
import java.awt.Component;

public class MenuKeyEvent extends KeyEvent {
    private MenuElement[] path;
    private MenuSelectionManager manager;
    
    public MenuKeyEvent(Component source, int id, long when, int modifiers, int keyCode, char keyChar, MenuElement[] p, MenuSelectionManager m) {
        super(source, id, when, modifiers, keyCode, keyChar);
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
