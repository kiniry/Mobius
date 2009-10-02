package javax.swing;

import java.awt.*;
import java.util.*;
import java.awt.event.*;
import javax.swing.event.*;

public class MenuSelectionManager {
    
    public MenuSelectionManager() {
        
    }
    private static final MenuSelectionManager instance = new MenuSelectionManager();
    private Vector selection = new Vector();
    private static final boolean TRACE = false;
    private static final boolean VERBOSE = false;
    private static final boolean DEBUG = false;
    
    public static MenuSelectionManager defaultManager() {
        return instance;
    }
    protected transient ChangeEvent changeEvent = null;
    protected EventListenerList listenerList = new EventListenerList();
    
    public void setSelectedPath(MenuElement[] path) {
        int i;
        int c;
        int currentSelectionCount = selection.size();
        int firstDifference = 0;
        if (path == null) {
            path = new MenuElement[0];
        }
        ;
        for (i = 0, c = path.length; i < c; i++) {
            if (i < currentSelectionCount && (MenuElement)(MenuElement)selection.elementAt(i) == path[i]) firstDifference++; else break;
        }
        for (i = currentSelectionCount - 1; i >= firstDifference; i--) {
            MenuElement me = (MenuElement)(MenuElement)selection.elementAt(i);
            selection.removeElementAt(i);
            me.menuSelectionChanged(false);
        }
        for (i = firstDifference, c = path.length; i < c; i++) {
            if (path[i] != null) {
                selection.addElement(path[i]);
                path[i].menuSelectionChanged(true);
            }
        }
        fireStateChanged();
    }
    
    public MenuElement[] getSelectedPath() {
        MenuElement[] res = new MenuElement[selection.size()];
        int i;
        int c;
        for (i = 0, c = selection.size(); i < c; i++) res[i] = (MenuElement)(MenuElement)selection.elementAt(i);
        return res;
    }
    
    public void clearSelectedPath() {
        if (selection.size() > 0) {
            setSelectedPath(null);
        }
    }
    
    public void addChangeListener(ChangeListener l) {
        listenerList.add(ChangeListener.class, l);
    }
    
    public void removeChangeListener(ChangeListener l) {
        listenerList.remove(ChangeListener.class, l);
    }
    
    public ChangeListener[] getChangeListeners() {
        return (ChangeListener[])(ChangeListener[])listenerList.getListeners(ChangeListener.class);
    }
    
    protected void fireStateChanged() {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ChangeListener.class) {
                if (changeEvent == null) changeEvent = new ChangeEvent(this);
                ((ChangeListener)(ChangeListener)listeners[i + 1]).stateChanged(changeEvent);
            }
        }
    }
    
    public void processMouseEvent(MouseEvent event) {
        int screenX;
        int screenY;
        Point p;
        int i;
        int c;
        int j;
        int d;
        Component mc;
        Rectangle r2;
        int cWidth;
        int cHeight;
        MenuElement menuElement;
        MenuElement[] subElements;
        MenuElement[] path;
        Vector tmp;
        int selectionSize;
        p = event.getPoint();
        Component source = (Component)(Component)event.getSource();
        if (!source.isShowing()) {
            return;
        }
        int type = event.getID();
        int modifiers = event.getModifiers();
        if ((type == MouseEvent.MOUSE_ENTERED || type == MouseEvent.MOUSE_EXITED) && ((modifiers & (InputEvent.BUTTON1_MASK | InputEvent.BUTTON2_MASK | InputEvent.BUTTON3_MASK)) != 0)) {
            return;
        }
        SwingUtilities.convertPointToScreen(p, source);
        screenX = p.x;
        screenY = p.y;
        tmp = (Vector)(Vector)selection.clone();
        selectionSize = tmp.size();
        boolean success = false;
        for (i = selectionSize - 1; i >= 0 && success == false; i--) {
            menuElement = (MenuElement)(MenuElement)tmp.elementAt(i);
            subElements = menuElement.getSubElements();
            path = null;
            for (j = 0, d = subElements.length; j < d && success == false; j++) {
                if (subElements[j] == null) continue;
                mc = subElements[j].getComponent();
                if (!mc.isShowing()) continue;
                if (mc instanceof JComponent) {
                    cWidth = ((JComponent)(JComponent)mc).getWidth();
                    cHeight = ((JComponent)(JComponent)mc).getHeight();
                } else {
                    r2 = mc.getBounds();
                    cWidth = r2.width;
                    cHeight = r2.height;
                }
                p.x = screenX;
                p.y = screenY;
                SwingUtilities.convertPointFromScreen(p, mc);
                if (p.x >= 0 && p.x < cWidth && p.y >= 0 && p.y < cHeight) {
                    int k;
                    if (path == null) {
                        path = new MenuElement[i + 2];
                        for (k = 0; k <= i; k++) path[k] = (MenuElement)(MenuElement)tmp.elementAt(k);
                    }
                    path[i + 1] = subElements[j];
                    MenuElement[] currentSelection = getSelectedPath();
                    if (currentSelection[currentSelection.length - 1] != path[i + 1] && (currentSelection.length < 2 || currentSelection[currentSelection.length - 2] != path[i + 1])) {
                        Component oldMC = currentSelection[currentSelection.length - 1].getComponent();
                        MouseEvent exitEvent = new MouseEvent(oldMC, MouseEvent.MOUSE_EXITED, event.getWhen(), event.getModifiers(), p.x, p.y, event.getClickCount(), event.isPopupTrigger());
                        currentSelection[currentSelection.length - 1].processMouseEvent(exitEvent, path, this);
                        MouseEvent enterEvent = new MouseEvent(mc, MouseEvent.MOUSE_ENTERED, event.getWhen(), event.getModifiers(), p.x, p.y, event.getClickCount(), event.isPopupTrigger());
                        subElements[j].processMouseEvent(enterEvent, path, this);
                    }
                    MouseEvent mouseEvent = new MouseEvent(mc, event.getID(), event.getWhen(), event.getModifiers(), p.x, p.y, event.getClickCount(), event.isPopupTrigger());
                    subElements[j].processMouseEvent(mouseEvent, path, this);
                    success = true;
                    event.consume();
                }
            }
        }
    }
    
    private void printMenuElementArray(MenuElement[] path) {
        printMenuElementArray(path, false);
    }
    
    private void printMenuElementArray(MenuElement[] path, boolean dumpStack) {
        System.out.println("Path is(");
        int i;
        int j;
        for (i = 0, j = path.length; i < j; i++) {
            for (int k = 0; k <= i; k++) System.out.print("  ");
            MenuElement me = (MenuElement)path[i];
            if (me instanceof JMenuItem) {
                System.out.println(((JMenuItem)(JMenuItem)me).getText() + ", ");
            } else if (me instanceof JMenuBar) {
                System.out.println("JMenuBar, ");
            } else if (me instanceof JPopupMenu) {
                System.out.println("JPopupMenu, ");
            } else if (me == null) {
                System.out.println("NULL , ");
            } else {
                System.out.println("" + me + ", ");
            }
        }
        System.out.println(")");
        if (dumpStack == true) Thread.dumpStack();
    }
    
    public Component componentForPoint(Component source, Point sourcePoint) {
        int screenX;
        int screenY;
        Point p = sourcePoint;
        int i;
        int c;
        int j;
        int d;
        Component mc;
        Rectangle r2;
        int cWidth;
        int cHeight;
        MenuElement menuElement;
        MenuElement[] subElements;
        Vector tmp;
        int selectionSize;
        SwingUtilities.convertPointToScreen(p, source);
        screenX = p.x;
        screenY = p.y;
        tmp = (Vector)(Vector)selection.clone();
        selectionSize = tmp.size();
        for (i = selectionSize - 1; i >= 0; i--) {
            menuElement = (MenuElement)(MenuElement)tmp.elementAt(i);
            subElements = menuElement.getSubElements();
            for (j = 0, d = subElements.length; j < d; j++) {
                if (subElements[j] == null) continue;
                mc = subElements[j].getComponent();
                if (!mc.isShowing()) continue;
                if (mc instanceof JComponent) {
                    cWidth = ((JComponent)(JComponent)mc).getWidth();
                    cHeight = ((JComponent)(JComponent)mc).getHeight();
                } else {
                    r2 = mc.getBounds();
                    cWidth = r2.width;
                    cHeight = r2.height;
                }
                p.x = screenX;
                p.y = screenY;
                SwingUtilities.convertPointFromScreen(p, mc);
                if (p.x >= 0 && p.x < cWidth && p.y >= 0 && p.y < cHeight) {
                    return mc;
                }
            }
        }
        return null;
    }
    
    public void processKeyEvent(KeyEvent e) {
        MenuElement[] sel2 = new MenuElement[0];
        sel2 = (MenuElement[])(MenuElement[])selection.toArray(sel2);
        int selSize = sel2.length;
        MenuElement[] path;
        if (selSize < 1) {
            return;
        }
        for (int i = selSize - 1; i >= 0; i--) {
            MenuElement elem = sel2[i];
            MenuElement[] subs = elem.getSubElements();
            path = null;
            for (int j = 0; j < subs.length; j++) {
                if (subs[j] == null || !subs[j].getComponent().isShowing() || !subs[j].getComponent().isEnabled()) {
                    continue;
                }
                if (path == null) {
                    path = new MenuElement[i + 2];
                    System.arraycopy(sel2, 0, path, 0, i + 1);
                }
                path[i + 1] = subs[j];
                subs[j].processKeyEvent(e, path, this);
                if (e.isConsumed()) {
                    return;
                }
            }
        }
        path = new MenuElement[1];
        path[0] = sel2[0];
        path[0].processKeyEvent(e, path, this);
        if (e.isConsumed()) {
            return;
        }
    }
    
    public boolean isComponentPartOfCurrentMenu(Component c) {
        if (selection.size() > 0) {
            MenuElement me = (MenuElement)(MenuElement)selection.elementAt(0);
            return isComponentPartOfCurrentMenu(me, c);
        } else return false;
    }
    
    private boolean isComponentPartOfCurrentMenu(MenuElement root, Component c) {
        MenuElement[] children;
        int i;
        int d;
        if (root == null) return false;
        if (root.getComponent() == c) return true; else {
            children = root.getSubElements();
            for (i = 0, d = children.length; i < d; i++) {
                if (isComponentPartOfCurrentMenu(children[i], c)) return true;
            }
        }
        return false;
    }
}
