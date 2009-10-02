package javax.swing.plaf.basic;

import sun.swing.UIAction;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;

class BasicMenuUI$Actions extends UIAction {
    private static final String SELECT = "selectMenu";
    private JMenu menu;
    private boolean force = false;
    
    BasicMenuUI$Actions(String key, JMenu menu, boolean shouldForce) {
        super(key);
        this.menu = menu;
        this.force = shouldForce;
    }
    
    private JMenu getMenu(ActionEvent e) {
        if (e.getSource() instanceof JMenu) {
            return (JMenu)(JMenu)e.getSource();
        }
        return menu;
    }
    
    public void actionPerformed(ActionEvent e) {
        JMenu menu = getMenu(e);
        if (!BasicMenuUI.access$100()) {
            JPopupMenu pm = BasicPopupMenuUI.getLastPopup();
            if (pm != null && pm != menu.getParent()) {
                return;
            }
        }
        final MenuSelectionManager defaultManager = MenuSelectionManager.defaultManager();
        if (force) {
            Container cnt = menu.getParent();
            if (cnt != null && cnt instanceof JMenuBar) {
                MenuElement[] me;
                MenuElement[] subElements;
                subElements = menu.getPopupMenu().getSubElements();
                if (subElements.length > 0) {
                    me = new MenuElement[4];
                    me[0] = (MenuElement)(MenuElement)cnt;
                    me[1] = (MenuElement)menu;
                    me[2] = (MenuElement)menu.getPopupMenu();
                    me[3] = subElements[0];
                } else {
                    me = new MenuElement[3];
                    me[0] = (MenuElement)(MenuElement)cnt;
                    me[1] = menu;
                    me[2] = (MenuElement)menu.getPopupMenu();
                }
                defaultManager.setSelectedPath(me);
            }
        } else {
            MenuElement[] path = defaultManager.getSelectedPath();
            if (path.length > 0 && path[path.length - 1] == menu) {
                BasicMenuUI.access$200(path, menu.getPopupMenu());
            }
        }
    }
    
    public boolean isEnabled(Object c) {
        if (c instanceof JMenu) {
            return ((JMenu)(JMenu)c).isEnabled();
        }
        return true;
    }
}
