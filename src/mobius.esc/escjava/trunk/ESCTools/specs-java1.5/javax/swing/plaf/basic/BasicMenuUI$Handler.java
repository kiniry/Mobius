package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import java.util.Arrays;
import java.util.ArrayList;

class BasicMenuUI$Handler extends BasicMenuItemUI$Handler implements MenuKeyListener {
    
    /*synthetic*/ BasicMenuUI$Handler(BasicMenuUI x0, javax.swing.plaf.basic.BasicMenuUI$1 x1) {
        this(x0);
    }
    /*synthetic*/ final BasicMenuUI this$0;
    
    private BasicMenuUI$Handler(/*synthetic*/ final BasicMenuUI this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        if (e.getPropertyName() == AbstractButton.MNEMONIC_CHANGED_PROPERTY) {
            this$0.updateMnemonicBinding();
        } else {
            if (e.getPropertyName().equals("ancestor")) {
                BasicMenuUI.access$300(this$0);
            }
            super.propertyChange(e);
        }
    }
    
    public void mouseClicked(MouseEvent e) {
    }
    
    public void mousePressed(MouseEvent e) {
        JMenu menu = (JMenu)(JMenu)this$0.menuItem;
        if (!menu.isEnabled()) return;
        MenuSelectionManager manager = MenuSelectionManager.defaultManager();
        if (menu.isTopLevelMenu()) {
            if (menu.isSelected()) {
                manager.clearSelectedPath();
            } else {
                Container cnt = menu.getParent();
                if (cnt != null && cnt instanceof JMenuBar) {
                    MenuElement[] me = new MenuElement[2];
                    me[0] = (MenuElement)(MenuElement)cnt;
                    me[1] = menu;
                    manager.setSelectedPath(me);
                }
            }
        }
        MenuElement[] selectedPath = manager.getSelectedPath();
        if (selectedPath.length > 0 && selectedPath[selectedPath.length - 1] != menu.getPopupMenu()) {
            if (menu.isTopLevelMenu() || menu.getDelay() == 0) {
                BasicMenuUI.access$200(selectedPath, menu.getPopupMenu());
            } else {
                this$0.setupPostTimer(menu);
            }
        }
    }
    
    public void mouseReleased(MouseEvent e) {
        JMenu menu = (JMenu)(JMenu)this$0.menuItem;
        if (!menu.isEnabled()) return;
        MenuSelectionManager manager = MenuSelectionManager.defaultManager();
        manager.processMouseEvent(e);
        if (!e.isConsumed()) manager.clearSelectedPath();
    }
    
    public void mouseEntered(MouseEvent e) {
        JMenu menu = (JMenu)(JMenu)this$0.menuItem;
        if (!menu.isEnabled()) return;
        MenuSelectionManager manager = MenuSelectionManager.defaultManager();
        MenuElement[] selectedPath = manager.getSelectedPath();
        if (!menu.isTopLevelMenu()) {
            if (!(selectedPath.length > 0 && selectedPath[selectedPath.length - 1] == menu.getPopupMenu())) {
                if (menu.getDelay() == 0) {
                    BasicMenuUI.access$200(this$0.getPath(), menu.getPopupMenu());
                } else {
                    manager.setSelectedPath(this$0.getPath());
                    this$0.setupPostTimer(menu);
                }
            }
        } else {
            if (selectedPath.length > 0 && selectedPath[0] == menu.getParent()) {
                MenuElement[] newPath = new MenuElement[3];
                newPath[0] = (MenuElement)(MenuElement)menu.getParent();
                newPath[1] = menu;
                newPath[2] = menu.getPopupMenu();
                manager.setSelectedPath(newPath);
            }
        }
    }
    
    public void mouseExited(MouseEvent e) {
    }
    
    public void mouseDragged(MouseEvent e) {
        JMenu menu = (JMenu)(JMenu)this$0.menuItem;
        if (!menu.isEnabled()) return;
        MenuSelectionManager.defaultManager().processMouseEvent(e);
    }
    
    public void mouseMoved(MouseEvent e) {
    }
    
    public void menuDragMouseEntered(MenuDragMouseEvent e) {
    }
    
    public void menuDragMouseDragged(MenuDragMouseEvent e) {
        if (this$0.menuItem.isEnabled() == false) return;
        MenuSelectionManager manager = e.getMenuSelectionManager();
        MenuElement[] path = e.getPath();
        Point p = e.getPoint();
        if (p.x >= 0 && p.x < this$0.menuItem.getWidth() && p.y >= 0 && p.y < this$0.menuItem.getHeight()) {
            JMenu menu = (JMenu)(JMenu)this$0.menuItem;
            MenuElement[] selectedPath = manager.getSelectedPath();
            if (!(selectedPath.length > 0 && selectedPath[selectedPath.length - 1] == menu.getPopupMenu())) {
                if (menu.isTopLevelMenu() || menu.getDelay() == 0 || e.getID() == MouseEvent.MOUSE_DRAGGED) {
                    BasicMenuUI.access$200(path, menu.getPopupMenu());
                } else {
                    manager.setSelectedPath(path);
                    this$0.setupPostTimer(menu);
                }
            }
        } else if (e.getID() == MouseEvent.MOUSE_RELEASED) {
            Component comp = manager.componentForPoint(e.getComponent(), e.getPoint());
            if (comp == null) manager.clearSelectedPath();
        }
    }
    
    public void menuDragMouseExited(MenuDragMouseEvent e) {
    }
    
    public void menuDragMouseReleased(MenuDragMouseEvent e) {
    }
    
    public void menuKeyTyped(MenuKeyEvent e) {
        if (!BasicMenuUI.access$100() && BasicPopupMenuUI.getLastPopup() != null) {
            return;
        }
        char key = Character.toLowerCase((char)this$0.menuItem.getMnemonic());
        MenuElement[] path = e.getPath();
        if (key == Character.toLowerCase(e.getKeyChar())) {
            JPopupMenu popupMenu = ((JMenu)(JMenu)this$0.menuItem).getPopupMenu();
            ArrayList newList = new ArrayList(Arrays.asList(path));
            newList.add(popupMenu);
            MenuElement[] subs = popupMenu.getSubElements();
            MenuElement sub = BasicPopupMenuUI.findEnabledChild(subs, -1, true);
            if (sub != null) {
                newList.add(sub);
            }
            MenuSelectionManager manager = e.getMenuSelectionManager();
            MenuElement[] newPath = new MenuElement[0];
            ;
            newPath = (MenuElement[])(MenuElement[])newList.toArray(newPath);
            manager.setSelectedPath(newPath);
            e.consume();
        }
    }
    
    public void menuKeyPressed(MenuKeyEvent e) {
    }
    
    public void menuKeyReleased(MenuKeyEvent e) {
    }
}
