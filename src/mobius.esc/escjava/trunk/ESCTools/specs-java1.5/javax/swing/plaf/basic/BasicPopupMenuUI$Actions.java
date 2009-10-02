package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.Component;
import java.awt.KeyboardFocusManager;
import java.awt.event.*;
import java.util.*;
import sun.swing.UIAction;

class BasicPopupMenuUI$Actions extends UIAction {
    private static final String CANCEL = "cancel";
    private static final String SELECT_NEXT = "selectNext";
    private static final String SELECT_PREVIOUS = "selectPrevious";
    private static final String SELECT_PARENT = "selectParent";
    private static final String SELECT_CHILD = "selectChild";
    private static final String RETURN = "return";
    private static final boolean FORWARD = true;
    private static final boolean BACKWARD = false;
    private static final boolean PARENT = false;
    private static final boolean CHILD = true;
    
    BasicPopupMenuUI$Actions(String key) {
        super(key);
    }
    
    public void actionPerformed(ActionEvent e) {
        String key = getName();
        if (key == CANCEL) {
            cancel();
        } else if (key == SELECT_NEXT) {
            selectItem(FORWARD);
        } else if (key == SELECT_PREVIOUS) {
            selectItem(BACKWARD);
        } else if (key == SELECT_PARENT) {
            selectParentChild(PARENT);
        } else if (key == SELECT_CHILD) {
            selectParentChild(CHILD);
        } else if (key == RETURN) {
            doReturn();
        }
    }
    
    private void doReturn() {
        KeyboardFocusManager fmgr = KeyboardFocusManager.getCurrentKeyboardFocusManager();
        Component focusOwner = fmgr.getFocusOwner();
        if (focusOwner != null && !(focusOwner instanceof JRootPane)) {
            return;
        }
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        MenuElement[] path = msm.getSelectedPath();
        MenuElement lastElement;
        if (path.length > 0) {
            lastElement = path[path.length - 1];
            if (lastElement instanceof JMenu) {
                MenuElement[] newPath = new MenuElement[path.length + 1];
                System.arraycopy(path, 0, newPath, 0, path.length);
                newPath[path.length] = ((JMenu)(JMenu)lastElement).getPopupMenu();
                msm.setSelectedPath(newPath);
            } else if (lastElement instanceof JMenuItem) {
                JMenuItem mi = (JMenuItem)(JMenuItem)lastElement;
                if (mi.getUI() instanceof BasicMenuItemUI) {
                    ((BasicMenuItemUI)(BasicMenuItemUI)mi.getUI()).doClick(msm);
                } else {
                    msm.clearSelectedPath();
                    mi.doClick(0);
                }
            }
        }
    }
    
    private void selectParentChild(boolean direction) {
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        MenuElement[] path = msm.getSelectedPath();
        int len = path.length;
        if (direction == PARENT) {
            int popupIndex = len - 1;
            if (len > 2 && (path[popupIndex] instanceof JPopupMenu || path[--popupIndex] instanceof JPopupMenu) && !((JMenu)(JMenu)path[popupIndex - 1]).isTopLevelMenu()) {
                MenuElement[] newPath = new MenuElement[popupIndex];
                System.arraycopy(path, 0, newPath, 0, popupIndex);
                msm.setSelectedPath(newPath);
                return;
            }
        } else {
            if (len > 0 && path[len - 1] instanceof JMenu && !((JMenu)(JMenu)path[len - 1]).isTopLevelMenu()) {
                JMenu menu = (JMenu)(JMenu)path[len - 1];
                JPopupMenu popup = menu.getPopupMenu();
                MenuElement[] subs = popup.getSubElements();
                MenuElement item = BasicPopupMenuUI.findEnabledChild(subs, -1, true);
                MenuElement[] newPath;
                if (item == null) {
                    newPath = new MenuElement[len + 1];
                } else {
                    newPath = new MenuElement[len + 2];
                    newPath[len + 1] = item;
                }
                System.arraycopy(path, 0, newPath, 0, len);
                newPath[len] = popup;
                msm.setSelectedPath(newPath);
                return;
            }
        }
        if (len > 1 && path[0] instanceof JMenuBar) {
            MenuElement currentMenu = path[1];
            MenuElement nextMenu = BasicPopupMenuUI.findEnabledChild(path[0].getSubElements(), currentMenu, direction);
            if (nextMenu != null && nextMenu != currentMenu) {
                MenuElement[] newSelection;
                if (len == 2) {
                    newSelection = new MenuElement[2];
                    newSelection[0] = path[0];
                    newSelection[1] = nextMenu;
                } else {
                    newSelection = new MenuElement[3];
                    newSelection[0] = path[0];
                    newSelection[1] = nextMenu;
                    newSelection[2] = ((JMenu)(JMenu)nextMenu).getPopupMenu();
                }
                msm.setSelectedPath(newSelection);
            }
        }
    }
    
    private void selectItem(boolean direction) {
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        MenuElement[] path = msm.getSelectedPath();
        if (path.length < 2) {
            return;
        }
        int len = path.length;
        if (path[0] instanceof JMenuBar && path[1] instanceof JMenu && len == 2) {
            JPopupMenu popup = ((JMenu)(JMenu)path[1]).getPopupMenu();
            MenuElement next = BasicPopupMenuUI.findEnabledChild(popup.getSubElements(), -1, FORWARD);
            MenuElement[] newPath;
            if (next != null) {
                newPath = new MenuElement[4];
                newPath[3] = next;
            } else {
                newPath = new MenuElement[3];
            }
            System.arraycopy(path, 0, newPath, 0, 2);
            newPath[2] = popup;
            msm.setSelectedPath(newPath);
        } else if (path[len - 1] instanceof JPopupMenu && path[len - 2] instanceof JMenu) {
            JMenu menu = (JMenu)(JMenu)path[len - 2];
            JPopupMenu popup = menu.getPopupMenu();
            MenuElement next = BasicPopupMenuUI.findEnabledChild(popup.getSubElements(), -1, direction);
            if (next != null) {
                MenuElement[] newPath = new MenuElement[len + 1];
                System.arraycopy(path, 0, newPath, 0, len);
                newPath[len] = next;
                msm.setSelectedPath(newPath);
            } else {
                if (len > 2 && path[len - 3] instanceof JPopupMenu) {
                    popup = ((JPopupMenu)(JPopupMenu)path[len - 3]);
                    next = BasicPopupMenuUI.findEnabledChild(popup.getSubElements(), menu, direction);
                    if (next != null && next != menu) {
                        MenuElement[] newPath = new MenuElement[len - 1];
                        System.arraycopy(path, 0, newPath, 0, len - 2);
                        newPath[len - 2] = next;
                        msm.setSelectedPath(newPath);
                    }
                }
            }
        } else {
            MenuElement[] subs = path[len - 2].getSubElements();
            MenuElement nextChild = BasicPopupMenuUI.findEnabledChild(subs, path[len - 1], direction);
            if (nextChild == null) {
                nextChild = BasicPopupMenuUI.findEnabledChild(subs, -1, direction);
            }
            if (nextChild != null) {
                path[len - 1] = nextChild;
                msm.setSelectedPath(path);
            }
        }
    }
    
    private void cancel() {
        JPopupMenu lastPopup = (JPopupMenu)BasicPopupMenuUI.getLastPopup();
        if (lastPopup != null) {
            lastPopup.putClientProperty("JPopupMenu.firePopupMenuCanceled", Boolean.TRUE);
        }
        MenuElement[] path = MenuSelectionManager.defaultManager().getSelectedPath();
        if (path.length > 4) {
            MenuElement[] newPath = new MenuElement[path.length - 2];
            System.arraycopy(path, 0, newPath, 0, path.length - 2);
            MenuSelectionManager.defaultManager().setSelectedPath(newPath);
        } else MenuSelectionManager.defaultManager().clearSelectedPath();
    }
}
