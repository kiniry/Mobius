package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.event.*;
import java.util.*;

class BasicPopupMenuUI$BasicMenuKeyListener implements MenuKeyListener {
    
    /*synthetic*/ BasicPopupMenuUI$BasicMenuKeyListener(BasicPopupMenuUI x0, javax.swing.plaf.basic.BasicPopupMenuUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicPopupMenuUI this$0;
    
    private BasicPopupMenuUI$BasicMenuKeyListener(/*synthetic*/ final BasicPopupMenuUI this$0) {
        this.this$0 = this$0;
        
    }
    MenuElement menuToOpen = null;
    
    public void menuKeyTyped(MenuKeyEvent e) {
        if (menuToOpen != null) {
            JPopupMenu subpopup = ((JMenu)(JMenu)menuToOpen).getPopupMenu();
            MenuElement subitem = BasicPopupMenuUI.findEnabledChild(subpopup.getSubElements(), -1, true);
            ArrayList lst = new ArrayList(Arrays.asList(e.getPath()));
            lst.add(menuToOpen);
            lst.add(subpopup);
            if (subitem != null) {
                lst.add(subitem);
            }
            MenuElement[] newPath = new MenuElement[0];
            ;
            newPath = (MenuElement[])(MenuElement[])lst.toArray(newPath);
            MenuSelectionManager.defaultManager().setSelectedPath(newPath);
            e.consume();
        }
        menuToOpen = null;
    }
    
    public void menuKeyPressed(MenuKeyEvent e) {
        if (!Character.isLetterOrDigit(e.getKeyChar())) {
            return;
        }
        int keyCode = e.getKeyCode();
        MenuSelectionManager manager = e.getMenuSelectionManager();
        MenuElement[] path = e.getPath();
        MenuElement[] items = this$0.popupMenu.getSubElements();
        int currentIndex = -1;
        int matches = 0;
        int firstMatch = -1;
        int[] indexes = null;
        for (int j = 0; j < items.length; j++) {
            if (!(items[j] instanceof JMenuItem)) {
                continue;
            }
            JMenuItem item = (JMenuItem)(JMenuItem)items[j];
            if (item.isEnabled() && item.isVisible() && keyCode == item.getMnemonic()) {
                if (matches == 0) {
                    firstMatch = j;
                    matches++;
                } else {
                    if (indexes == null) {
                        indexes = new int[items.length];
                        indexes[0] = firstMatch;
                    }
                    indexes[matches++] = j;
                }
            }
            if (item.isArmed()) {
                currentIndex = matches - 1;
            }
        }
        if (matches == 0) {
            ;
        } else if (matches == 1) {
            JMenuItem item = (JMenuItem)(JMenuItem)items[firstMatch];
            if (item instanceof JMenu) {
                menuToOpen = item;
            } else if (item.isEnabled()) {
                manager.clearSelectedPath();
                item.doClick();
            }
            e.consume();
        } else {
            MenuElement newItem = null;
            newItem = items[indexes[(currentIndex + 1) % matches]];
            MenuElement[] newPath = new MenuElement[path.length + 1];
            System.arraycopy(path, 0, newPath, 0, path.length);
            newPath[path.length] = newItem;
            manager.setSelectedPath(newPath);
            e.consume();
        }
        return;
    }
    
    public void menuKeyReleased(MenuKeyEvent e) {
    }
}
