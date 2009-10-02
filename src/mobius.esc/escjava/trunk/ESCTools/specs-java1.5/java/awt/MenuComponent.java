package java.awt;

import java.awt.peer.MenuComponentPeer;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.io.ObjectInputStream;
import sun.awt.AppContext;
import javax.accessibility.*;

public abstract class MenuComponent implements java.io.Serializable {
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    transient MenuComponentPeer peer;
    transient MenuContainer parent;
    transient AppContext appContext;
    Font font;
    private String name;
    private boolean nameExplicitlySet = false;
    boolean newEventsOnly = false;
    static final String actionListenerK = Component.actionListenerK;
    static final String itemListenerK = Component.itemListenerK;
    private static final long serialVersionUID = -4536902356223894379L;
    private transient Object privateKey = new Object();
    
    public MenuComponent() throws HeadlessException {
        
        GraphicsEnvironment.checkHeadless();
        appContext = AppContext.getAppContext();
    }
    
    String constructComponentName() {
        return null;
    }
    
    public String getName() {
        if (name == null && !nameExplicitlySet) {
            synchronized (this) {
                if (name == null && !nameExplicitlySet) name = constructComponentName();
            }
        }
        return name;
    }
    
    public void setName(String name) {
        synchronized (this) {
            this.name = name;
            nameExplicitlySet = true;
        }
    }
    
    public MenuContainer getParent() {
        return getParent_NoClientCode();
    }
    
    final MenuContainer getParent_NoClientCode() {
        return parent;
    }
    
    
    public MenuComponentPeer getPeer() {
        return peer;
    }
    
    public Font getFont() {
        Font font = this.font;
        if (font != null) {
            return font;
        }
        MenuContainer parent = this.parent;
        if (parent != null) {
            return parent.getFont();
        }
        return null;
    }
    
    final Font getFont_NoClientCode() {
        Font font = this.font;
        if (font != null) {
            return font;
        }
        Object parent = this.parent;
        if (parent != null) {
            if (parent instanceof Component) {
                font = ((Component)(Component)parent).getFont_NoClientCode();
            } else if (parent instanceof MenuComponent) {
                font = ((MenuComponent)(MenuComponent)parent).getFont_NoClientCode();
            }
        }
        return font;
    }
    
    public void setFont(Font f) {
        font = f;
        if (peer != null) {
            peer.setFont(f);
        }
    }
    
    public void removeNotify() {
        synchronized (getTreeLock()) {
            MenuComponentPeer p = (MenuComponentPeer)this.peer;
            if (p != null) {
                Toolkit.getEventQueue().removeSourceEvents(this, true);
                this.peer = null;
                p.dispose();
            }
        }
    }
    
    
    public boolean postEvent(Event evt) {
        MenuContainer parent = this.parent;
        if (parent != null) {
            parent.postEvent(evt);
        }
        return false;
    }
    
    public final void dispatchEvent(AWTEvent e) {
        dispatchEventImpl(e);
    }
    
    void dispatchEventImpl(AWTEvent e) {
        EventQueue.setCurrentEventAndMostRecentTime(e);
        Toolkit.getDefaultToolkit().notifyAWTEventListeners(e);
        if (newEventsOnly || (parent != null && parent instanceof MenuComponent && ((MenuComponent)(MenuComponent)parent).newEventsOnly)) {
            if (eventEnabled(e)) {
                processEvent(e);
            } else if (e instanceof ActionEvent && parent != null) {
                e.setSource(parent);
                ((MenuComponent)(MenuComponent)parent).dispatchEvent(e);
            }
        } else {
            Event olde = e.convertToOld();
            if (olde != null) {
                postEvent(olde);
            }
        }
    }
    
    boolean eventEnabled(AWTEvent e) {
        return false;
    }
    
    protected void processEvent(AWTEvent e) {
    }
    
    protected String paramString() {
        String thisName = getName();
        return (thisName != null ? thisName : "");
    }
    
    public String toString() {
        return getClass().getName() + "[" + paramString() + "]";
    }
    
    protected final Object getTreeLock() {
        return Component.LOCK;
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        GraphicsEnvironment.checkHeadless();
        s.defaultReadObject();
        privateKey = new Object();
        appContext = AppContext.getAppContext();
    }
    
    private static native void initIDs();
    AccessibleContext accessibleContext = null;
    
    public AccessibleContext getAccessibleContext() {
        return accessibleContext;
    }
    {
    }
    
    int getAccessibleIndexInParent() {
        MenuContainer localParent = parent;
        if (!(localParent instanceof MenuComponent)) {
            return -1;
        }
        MenuComponent localParentMenu = (MenuComponent)(MenuComponent)localParent;
        return localParentMenu.getAccessibleChildIndex(this);
    }
    
    int getAccessibleChildIndex(MenuComponent child) {
        return -1;
    }
    
    AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = new AccessibleStateSet();
        return states;
    }
}
