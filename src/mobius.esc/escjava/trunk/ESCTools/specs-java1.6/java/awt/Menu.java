package java.awt;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.util.Vector;
import java.util.Enumeration;
import java.awt.peer.MenuPeer;
import java.awt.event.KeyEvent;
import javax.accessibility.*;

public class Menu extends MenuItem implements MenuContainer, Accessible {
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    Vector items = new Vector();
    boolean tearOff;
    boolean isHelpMenu;
    private static final String base = "menu";
    private static int nameCounter = 0;
    private static final long serialVersionUID = -8809584163345499784L;
    
    public Menu() throws HeadlessException {
        this("", false);
    }
    
    public Menu(String label) throws HeadlessException {
        this(label, false);
    }
    
    public Menu(String label, boolean tearOff) throws HeadlessException {
        super(label);
        this.tearOff = tearOff;
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) peer = Toolkit.getDefaultToolkit().createMenu(this);
            int nitems = getItemCount();
            for (int i = 0; i < nitems; i++) {
                MenuItem mi = getItem(i);
                mi.parent = this;
                mi.addNotify();
            }
        }
    }
    
    public void removeNotify() {
        synchronized (getTreeLock()) {
            int nitems = getItemCount();
            for (int i = 0; i < nitems; i++) {
                getItem(i).removeNotify();
            }
            super.removeNotify();
        }
    }
    
    public boolean isTearOff() {
        return tearOff;
    }
    
    public int getItemCount() {
        return countItems();
    }
    
    
    public int countItems() {
        return countItemsImpl();
    }
    
    final int countItemsImpl() {
        return items.size();
    }
    
    public MenuItem getItem(int index) {
        return getItemImpl(index);
    }
    
    final MenuItem getItemImpl(int index) {
        return (MenuItem)(MenuItem)items.elementAt(index);
    }
    
    public MenuItem add(MenuItem mi) {
        synchronized (getTreeLock()) {
            if (mi.parent != null) {
                mi.parent.remove(mi);
            }
            items.addElement(mi);
            mi.parent = this;
            MenuPeer peer = (MenuPeer)(MenuPeer)this.peer;
            if (peer != null) {
                mi.addNotify();
                peer.addItem(mi);
            }
            return mi;
        }
    }
    
    public void add(String label) {
        add(new MenuItem(label));
    }
    
    public void insert(MenuItem menuitem, int index) {
        synchronized (getTreeLock()) {
            if (index < 0) {
                throw new IllegalArgumentException("index less than zero.");
            }
            int nitems = getItemCount();
            Vector tempItems = new Vector();
            for (int i = index; i < nitems; i++) {
                tempItems.addElement(getItem(index));
                remove(index);
            }
            add(menuitem);
            for (int i = 0; i < tempItems.size(); i++) {
                add((MenuItem)(MenuItem)tempItems.elementAt(i));
            }
        }
    }
    
    public void insert(String label, int index) {
        insert(new MenuItem(label), index);
    }
    
    public void addSeparator() {
        add("-");
    }
    
    public void insertSeparator(int index) {
        synchronized (getTreeLock()) {
            if (index < 0) {
                throw new IllegalArgumentException("index less than zero.");
            }
            int nitems = getItemCount();
            Vector tempItems = new Vector();
            for (int i = index; i < nitems; i++) {
                tempItems.addElement(getItem(index));
                remove(index);
            }
            addSeparator();
            for (int i = 0; i < tempItems.size(); i++) {
                add((MenuItem)(MenuItem)tempItems.elementAt(i));
            }
        }
    }
    
    public void remove(int index) {
        synchronized (getTreeLock()) {
            MenuItem mi = getItem(index);
            items.removeElementAt(index);
            MenuPeer peer = (MenuPeer)(MenuPeer)this.peer;
            if (peer != null) {
                mi.removeNotify();
                mi.parent = null;
                peer.delItem(index);
            }
        }
    }
    
    public void remove(MenuComponent item) {
        synchronized (getTreeLock()) {
            int index = items.indexOf(item);
            if (index >= 0) {
                remove(index);
            }
        }
    }
    
    public void removeAll() {
        synchronized (getTreeLock()) {
            int nitems = getItemCount();
            for (int i = nitems - 1; i >= 0; i--) {
                remove(i);
            }
        }
    }
    
    boolean handleShortcut(KeyEvent e) {
        int nitems = getItemCount();
        for (int i = 0; i < nitems; i++) {
            MenuItem mi = getItem(i);
            if (mi.handleShortcut(e)) {
                return true;
            }
        }
        return false;
    }
    
    MenuItem getShortcutMenuItem(MenuShortcut s) {
        int nitems = getItemCount();
        for (int i = 0; i < nitems; i++) {
            MenuItem mi = getItem(i).getShortcutMenuItem(s);
            if (mi != null) {
                return mi;
            }
        }
        return null;
    }
    
    synchronized Enumeration shortcuts() {
        Vector shortcuts = new Vector();
        int nitems = getItemCount();
        for (int i = 0; i < nitems; i++) {
            MenuItem mi = getItem(i);
            if (mi instanceof Menu) {
                Enumeration e = ((Menu)(Menu)mi).shortcuts();
                while (e.hasMoreElements()) {
                    shortcuts.addElement(e.nextElement());
                }
            } else {
                MenuShortcut ms = mi.getShortcut();
                if (ms != null) {
                    shortcuts.addElement(ms);
                }
            }
        }
        return shortcuts.elements();
    }
    
    void deleteShortcut(MenuShortcut s) {
        int nitems = getItemCount();
        for (int i = 0; i < nitems; i++) {
            getItem(i).deleteShortcut(s);
        }
    }
    private int menuSerializedDataVersion = 1;
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.io.IOException {
        s.defaultWriteObject();
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException, HeadlessException {
        s.defaultReadObject();
        for (int i = 0; i < items.size(); i++) {
            MenuItem item = (MenuItem)(MenuItem)items.elementAt(i);
            item.parent = this;
        }
    }
    
    public String paramString() {
        String str = ",tearOff=" + tearOff + ",isHelpMenu=" + isHelpMenu;
        return super.paramString() + str;
    }
    
    private static native void initIDs();
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Menu$AccessibleAWTMenu(this);
        }
        return accessibleContext;
    }
    
    int getAccessibleChildIndex(MenuComponent child) {
        return items.indexOf(child);
    }
    {
    }
}
