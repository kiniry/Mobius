package java.awt;

import java.awt.peer.MenuItemPeer;
import java.awt.event.*;
import java.util.EventListener;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import javax.accessibility.*;

public class MenuItem extends MenuComponent implements Accessible {
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    boolean enabled = true;
    String label;
    String actionCommand;
    long eventMask;
    transient ActionListener actionListener;
    private MenuShortcut shortcut = null;
    private static final String base = "menuitem";
    private static int nameCounter = 0;
    private static final long serialVersionUID = -21757335363267194L;
    
    public MenuItem() throws HeadlessException {
        this("", null);
    }
    
    public MenuItem(String label) throws HeadlessException {
        this(label, null);
    }
    
    public MenuItem(String label, MenuShortcut s) throws HeadlessException {
        
        this.label = label;
        this.shortcut = s;
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) peer = Toolkit.getDefaultToolkit().createMenuItem(this);
        }
    }
    
    public String getLabel() {
        return label;
    }
    
    public synchronized void setLabel(String label) {
        this.label = label;
        MenuItemPeer peer = (MenuItemPeer)(MenuItemPeer)this.peer;
        if (peer != null) {
            peer.setLabel(label);
        }
    }
    
    public boolean isEnabled() {
        return enabled;
    }
    
    public synchronized void setEnabled(boolean b) {
        enable(b);
    }
    
    
    public synchronized void enable() {
        enabled = true;
        MenuItemPeer peer = (MenuItemPeer)(MenuItemPeer)this.peer;
        if (peer != null) {
            peer.enable();
        }
    }
    
    
    public void enable(boolean b) {
        if (b) {
            enable();
        } else {
            disable();
        }
    }
    
    
    public synchronized void disable() {
        enabled = false;
        MenuItemPeer peer = (MenuItemPeer)(MenuItemPeer)this.peer;
        if (peer != null) {
            peer.disable();
        }
    }
    
    public MenuShortcut getShortcut() {
        return shortcut;
    }
    
    public void setShortcut(MenuShortcut s) {
        shortcut = s;
        MenuItemPeer peer = (MenuItemPeer)(MenuItemPeer)this.peer;
        if (peer != null) {
            peer.setLabel(label);
        }
    }
    
    public void deleteShortcut() {
        shortcut = null;
        MenuItemPeer peer = (MenuItemPeer)(MenuItemPeer)this.peer;
        if (peer != null) {
            peer.setLabel(label);
        }
    }
    
    void deleteShortcut(MenuShortcut s) {
        if (s.equals(shortcut)) {
            shortcut = null;
            MenuItemPeer peer = (MenuItemPeer)(MenuItemPeer)this.peer;
            if (peer != null) {
                peer.setLabel(label);
            }
        }
    }
    
    void doMenuEvent(long when, int modifiers) {
        Toolkit.getEventQueue().postEvent(new ActionEvent(this, ActionEvent.ACTION_PERFORMED, getActionCommand(), when, modifiers));
    }
    
    boolean handleShortcut(KeyEvent e) {
        MenuShortcut s = new MenuShortcut(e.getKeyCode(), (e.getModifiers() & InputEvent.SHIFT_MASK) > 0);
        if (s.equals(shortcut) && enabled) {
            if (e.getID() == KeyEvent.KEY_PRESSED) {
                doMenuEvent(e.getWhen(), e.getModifiers());
            } else {
            }
            return true;
        }
        return false;
    }
    
    MenuItem getShortcutMenuItem(MenuShortcut s) {
        return (s.equals(shortcut)) ? this : null;
    }
    
    protected final void enableEvents(long eventsToEnable) {
        eventMask |= eventsToEnable;
        newEventsOnly = true;
    }
    
    protected final void disableEvents(long eventsToDisable) {
        eventMask &= ~eventsToDisable;
    }
    
    public void setActionCommand(String command) {
        actionCommand = command;
    }
    
    public String getActionCommand() {
        return getActionCommandImpl();
    }
    
    final String getActionCommandImpl() {
        return (actionCommand == null ? label : actionCommand);
    }
    
    public synchronized void addActionListener(ActionListener l) {
        if (l == null) {
            return;
        }
        actionListener = AWTEventMulticaster.add(actionListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void removeActionListener(ActionListener l) {
        if (l == null) {
            return;
        }
        actionListener = AWTEventMulticaster.remove(actionListener, l);
    }
    
    public synchronized ActionListener[] getActionListeners() {
        return (ActionListener[])((ActionListener[])getListeners(ActionListener.class));
    }
    
    public EventListener[] getListeners(Class listenerType) {
        EventListener l = null;
        if (listenerType == ActionListener.class) {
            l = actionListener;
        }
        return AWTEventMulticaster.getListeners(l, listenerType);
    }
    
    protected void processEvent(AWTEvent e) {
        if (e instanceof ActionEvent) {
            processActionEvent((ActionEvent)(ActionEvent)e);
        }
    }
    
    boolean eventEnabled(AWTEvent e) {
        if (e.id == ActionEvent.ACTION_PERFORMED) {
            if ((eventMask & AWTEvent.ACTION_EVENT_MASK) != 0 || actionListener != null) {
                return true;
            }
            return false;
        }
        return super.eventEnabled(e);
    }
    
    protected void processActionEvent(ActionEvent e) {
        ActionListener listener = actionListener;
        if (listener != null) {
            listener.actionPerformed(e);
        }
    }
    
    public String paramString() {
        String str = ",label=" + label;
        if (shortcut != null) {
            str += ",shortcut=" + shortcut;
        }
        return super.paramString() + str;
    }
    private int menuItemSerializedDataVersion = 1;
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        AWTEventMulticaster.save(s, actionListenerK, actionListener);
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        s.defaultReadObject();
        Object keyOrNull;
        while (null != (keyOrNull = s.readObject())) {
            String key = ((String)(String)keyOrNull).intern();
            if (actionListenerK == key) addActionListener((ActionListener)((ActionListener)s.readObject())); else s.readObject();
        }
    }
    
    private static native void initIDs();
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new MenuItem$AccessibleAWTMenuItem(this);
        }
        return accessibleContext;
    }
    {
    }
}
