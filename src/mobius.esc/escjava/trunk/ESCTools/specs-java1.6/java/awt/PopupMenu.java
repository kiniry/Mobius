package java.awt;

import java.awt.peer.PopupMenuPeer;
import javax.accessibility.*;

public class PopupMenu extends Menu {
    private static final String base = "popup";
    static int nameCounter = 0;
    private static final long serialVersionUID = -4620452533522760060L;
    
    public PopupMenu() throws HeadlessException {
        this("");
    }
    
    public PopupMenu(String label) throws HeadlessException {
        super(label);
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (parent != null && !(parent instanceof Component)) {
                super.addNotify();
            } else {
                if (peer == null) peer = Toolkit.getDefaultToolkit().createPopupMenu(this);
                int nitems = getItemCount();
                for (int i = 0; i < nitems; i++) {
                    MenuItem mi = getItem(i);
                    mi.parent = this;
                    mi.addNotify();
                }
            }
        }
    }
    
    public void show(Component origin, int x, int y) {
        MenuContainer localParent = parent;
        if (localParent == null) {
            throw new NullPointerException("parent is null");
        }
        if (!(localParent instanceof Component)) {
            throw new IllegalArgumentException("PopupMenus with non-Component parents cannot be shown");
        }
        Component compParent = (Component)(Component)localParent;
        if (compParent != origin && compParent instanceof Container && !((Container)(Container)compParent).isAncestorOf(origin)) {
            throw new IllegalArgumentException("origin not in parent\'s hierarchy");
        }
        if (compParent.getPeer() == null || !compParent.isShowing()) {
            throw new RuntimeException("parent not showing on screen");
        }
        if (peer == null) {
            addNotify();
        }
        synchronized (getTreeLock()) {
            if (peer != null) {
                ((PopupMenuPeer)(PopupMenuPeer)peer).show(new Event(origin, 0, Event.MOUSE_DOWN, x, y, 0, 0));
            }
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new PopupMenu$AccessibleAWTPopupMenu(this);
        }
        return accessibleContext;
    }
    {
    }
}
