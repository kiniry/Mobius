package java.awt;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.Vector;
import java.util.Enumeration;
import java.awt.peer.MenuBarPeer;
import java.awt.event.KeyEvent;
import javax.accessibility.*;

public class MenuBar extends MenuComponent implements MenuContainer, Accessible {
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    Vector menus = new Vector();
    Menu helpMenu;
    private static final String base = "menubar";
    private static int nameCounter = 0;
    private static final long serialVersionUID = -4930327919388951260L;
    
    public MenuBar() throws HeadlessException {
        
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) peer = Toolkit.getDefaultToolkit().createMenuBar(this);
            int nmenus = getMenuCount();
            for (int i = 0; i < nmenus; i++) {
                getMenu(i).addNotify();
            }
        }
    }
    
    public void removeNotify() {
        synchronized (getTreeLock()) {
            int nmenus = getMenuCount();
            for (int i = 0; i < nmenus; i++) {
                getMenu(i).removeNotify();
            }
            super.removeNotify();
        }
    }
    
    public Menu getHelpMenu() {
        return helpMenu;
    }
    
    public void setHelpMenu(Menu m) {
        synchronized (getTreeLock()) {
            if (helpMenu == m) {
                return;
            }
            if (helpMenu != null) {
                remove(helpMenu);
            }
            if (m.parent != this) {
                add(m);
            }
            helpMenu = m;
            if (m != null) {
                m.isHelpMenu = true;
                m.parent = this;
                MenuBarPeer peer = (MenuBarPeer)(MenuBarPeer)this.peer;
                if (peer != null) {
                    if (m.peer == null) {
                        m.addNotify();
                    }
                    peer.addHelpMenu(m);
                }
            }
        }
    }
    
    public Menu add(Menu m) {
        synchronized (getTreeLock()) {
            if (m.parent != null) {
                m.parent.remove(m);
            }
            menus.addElement(m);
            m.parent = this;
            MenuBarPeer peer = (MenuBarPeer)(MenuBarPeer)this.peer;
            if (peer != null) {
                if (m.peer == null) {
                    m.addNotify();
                }
                peer.addMenu(m);
            }
            return m;
        }
    }
    
    public void remove(int index) {
        synchronized (getTreeLock()) {
            Menu m = getMenu(index);
            menus.removeElementAt(index);
            MenuBarPeer peer = (MenuBarPeer)(MenuBarPeer)this.peer;
            if (peer != null) {
                m.removeNotify();
                m.parent = null;
                peer.delMenu(index);
            }
        }
    }
    
    public void remove(MenuComponent m) {
        synchronized (getTreeLock()) {
            int index = menus.indexOf(m);
            if (index >= 0) {
                remove(index);
            }
        }
    }
    
    public int getMenuCount() {
        return countMenus();
    }
    
    
    public int countMenus() {
        return getMenuCountImpl();
    }
    
    final int getMenuCountImpl() {
        return menus.size();
    }
    
    public Menu getMenu(int i) {
        return getMenuImpl(i);
    }
    
    final Menu getMenuImpl(int i) {
        return (Menu)(Menu)menus.elementAt(i);
    }
    
    public synchronized Enumeration shortcuts() {
        Vector shortcuts = new Vector();
        int nmenus = getMenuCount();
        for (int i = 0; i < nmenus; i++) {
            Enumeration e = getMenu(i).shortcuts();
            while (e.hasMoreElements()) {
                shortcuts.addElement(e.nextElement());
            }
        }
        return shortcuts.elements();
    }
    
    public MenuItem getShortcutMenuItem(MenuShortcut s) {
        int nmenus = getMenuCount();
        for (int i = 0; i < nmenus; i++) {
            MenuItem mi = getMenu(i).getShortcutMenuItem(s);
            if (mi != null) {
                return mi;
            }
        }
        return null;
    }
    
    boolean handleShortcut(KeyEvent e) {
        int id = e.getID();
        if (id != KeyEvent.KEY_PRESSED && id != KeyEvent.KEY_RELEASED) {
            return false;
        }
        int accelKey = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();
        if ((e.getModifiers() & accelKey) == 0) {
            return false;
        }
        int nmenus = getMenuCount();
        for (int i = 0; i < nmenus; i++) {
            Menu m = getMenu(i);
            if (m.handleShortcut(e)) {
                return true;
            }
        }
        return false;
    }
    
    public void deleteShortcut(MenuShortcut s) {
        int nmenus = getMenuCount();
        for (int i = 0; i < nmenus; i++) {
            getMenu(i).deleteShortcut(s);
        }
    }
    private int menuBarSerializedDataVersion = 1;
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.lang.ClassNotFoundException, java.io.IOException {
        s.defaultWriteObject();
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        s.defaultReadObject();
        for (int i = 0; i < menus.size(); i++) {
            Menu m = (Menu)(Menu)menus.elementAt(i);
            m.parent = this;
        }
    }
    
    private static native void initIDs();
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new MenuBar$AccessibleAWTMenuBar(this);
        }
        return accessibleContext;
    }
    
    int getAccessibleChildIndex(MenuComponent child) {
        return menus.indexOf(child);
    }
    {
    }
}
