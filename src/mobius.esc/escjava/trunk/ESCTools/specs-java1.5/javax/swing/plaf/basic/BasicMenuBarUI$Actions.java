package javax.swing.plaf.basic;

import sun.swing.UIAction;
import javax.swing.*;
import javax.swing.event.*;
import java.awt.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicMenuBarUI$Actions extends UIAction {
    private static final String TAKE_FOCUS = "takeFocus";
    
    BasicMenuBarUI$Actions(String key) {
        super(key);
    }
    
    public void actionPerformed(ActionEvent e) {
        JMenuBar menuBar = (JMenuBar)(JMenuBar)e.getSource();
        MenuSelectionManager defaultManager = MenuSelectionManager.defaultManager();
        MenuElement[] me;
        MenuElement[] subElements;
        JMenu menu = menuBar.getMenu(0);
        if (menu != null) {
            me = new MenuElement[3];
            me[0] = (MenuElement)menuBar;
            me[1] = (MenuElement)menu;
            me[2] = (MenuElement)menu.getPopupMenu();
            defaultManager.setSelectedPath(me);
        }
    }
}
