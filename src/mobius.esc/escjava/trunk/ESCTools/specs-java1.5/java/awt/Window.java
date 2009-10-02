package java.awt;

import java.applet.Applet;
import java.awt.peer.WindowPeer;
import java.awt.peer.ComponentPeer;
import java.awt.event.*;
import java.awt.image.BufferStrategy;
import java.util.Vector;
import java.util.Locale;
import java.util.EventListener;
import java.util.Set;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import java.io.OptionalDataException;
import java.awt.im.InputContext;
import java.util.ResourceBundle;
import java.lang.ref.WeakReference;
import java.lang.reflect.InvocationTargetException;
import java.security.AccessController;
import javax.accessibility.*;
import java.beans.PropertyChangeListener;
import sun.security.action.GetPropertyAction;
import sun.security.util.SecurityConstants;
import sun.awt.DebugHelper;

public class Window extends Container implements Accessible {
    
    /*synthetic*/ static Object access$000(Window x0) {
        return x0.inputContextLock;
    }
    String warningString;
    private transient Component temporaryLostComponent;
    static boolean systemSyncLWRequests = false;
    boolean syncLWRequests = false;
    transient boolean beforeFirstShow = true;
    static final int OPENED = 1;
    int state;
    private boolean alwaysOnTop;
    transient Vector ownedWindowList = new Vector();
    private transient WeakReference weakThis;
    transient boolean showWithParent;
    transient WindowListener windowListener;
    transient WindowStateListener windowStateListener;
    transient WindowFocusListener windowFocusListener;
    transient InputContext inputContext;
    private transient Object inputContextLock = new Object();
    private FocusManager focusMgr;
    private boolean focusableWindowState = true;
    private static final String base = "win";
    private static int nameCounter = 0;
    private static final long serialVersionUID = 4497834738069338734L;
    private static final DebugHelper dbg = DebugHelper.create(Window.class);
    private static final boolean locationByPlatformProp;
    private transient boolean modalExcluded = false;
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
        String s = (String)(String)java.security.AccessController.doPrivileged(new GetPropertyAction("java.awt.syncLWRequests"));
        systemSyncLWRequests = (s != null && s.equals("true"));
        s = (String)(String)java.security.AccessController.doPrivileged(new GetPropertyAction("java.awt.Window.locationByPlatform"));
        locationByPlatformProp = (s != null && s.equals("true"));
    }
    
    private static native void initIDs();
    
    Window(GraphicsConfiguration gc) {
        
        init(gc);
    }
    
    private void init(GraphicsConfiguration gc) {
        if (GraphicsEnvironment.isHeadless()) {
            throw new IllegalArgumentException("headless environment");
        }
        syncLWRequests = systemSyncLWRequests;
        setWarningString();
        this.cursor = Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR);
        this.visible = false;
        if (gc == null) {
            this.graphicsConfig = GraphicsEnvironment.getLocalGraphicsEnvironment().getDefaultScreenDevice().getDefaultConfiguration();
        } else {
            this.graphicsConfig = gc;
        }
        if (graphicsConfig.getDevice().getType() != GraphicsDevice.TYPE_RASTER_SCREEN) {
            throw new IllegalArgumentException("not a screen device");
        }
        setLayout(new BorderLayout());
        Rectangle screenBounds = graphicsConfig.getBounds();
        Insets screenInsets = getToolkit().getScreenInsets(graphicsConfig);
        int x = getX() + screenBounds.x + screenInsets.left;
        int y = getY() + screenBounds.y + screenInsets.top;
        if (x != this.x || y != this.y) {
            setLocation(x, y);
            setLocationByPlatform(locationByPlatformProp);
        }
    }
    
    Window() throws HeadlessException {
        
        GraphicsEnvironment.checkHeadless();
        init((GraphicsConfiguration)null);
    }
    
    public Window(Frame owner) {
        this(owner == null ? (GraphicsConfiguration)null : owner.getGraphicsConfiguration());
        ownedInit(owner);
    }
    
    public Window(Window owner) {
        this(owner == null ? (GraphicsConfiguration)null : owner.getGraphicsConfiguration());
        ownedInit(owner);
    }
    
    public Window(Window owner, GraphicsConfiguration gc) {
        this(gc);
        ownedInit(owner);
    }
    
    private void ownedInit(Window owner) {
        if (owner == null) {
            throw new IllegalArgumentException("null owner window");
        }
        this.parent = owner;
        this.weakThis = new WeakReference(this);
        owner.addOwnedWindow(weakThis);
        modalExcluded = owner.modalExcluded;
    }
    
    protected void finalize() throws Throwable {
        if (parent != null) {
            ((Window)(Window)parent).removeOwnedWindow(weakThis);
        }
        super.finalize();
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            Container parent = this.parent;
            if (parent != null && parent.getPeer() == null) {
                parent.addNotify();
            }
            if (peer == null) peer = getToolkit().createWindow(this);
            super.addNotify();
        }
    }
    
    public void pack() {
        Container parent = this.parent;
        if (parent != null && parent.getPeer() == null) {
            parent.addNotify();
        }
        if (peer == null) {
            addNotify();
        }
        Dimension newSize = getPreferredSize();
        if (peer != null) {
            setClientSize(newSize.width, newSize.height);
        }
        if (beforeFirstShow) {
            isPacked = true;
        }
        validate();
    }
    
    void setClientSize(int w, int h) {
        synchronized (getTreeLock()) {
            setBoundsOp(ComponentPeer.SET_CLIENT_SIZE);
            setBounds(x, y, w, h);
        }
    }
    
    
    public void show() {
        if (peer == null) {
            addNotify();
        }
        validate();
        if (visible) {
            toFront();
        } else {
            beforeFirstShow = false;
            super.show();
            locationByPlatform = false;
            for (int i = 0; i < ownedWindowList.size(); i++) {
                Window child = (Window)((WeakReference)ownedWindowList.elementAt(i)).get();
                if ((child != null) && child.showWithParent) {
                    child.show();
                    child.showWithParent = false;
                }
            }
            if (this instanceof Frame || this instanceof Dialog) {
                updateChildFocusableWindowState(this);
            }
        }
        if ((state & OPENED) == 0) {
            postWindowEvent(WindowEvent.WINDOW_OPENED);
            state |= OPENED;
        }
    }
    
    static void updateChildFocusableWindowState(Window w) {
        if (w.getPeer() != null && w.isShowing()) {
            ((WindowPeer)(WindowPeer)w.getPeer()).updateFocusableWindowState();
        }
        for (int i = 0; i < w.ownedWindowList.size(); i++) {
            Window child = (Window)((WeakReference)w.ownedWindowList.elementAt(i)).get();
            if (child != null) {
                updateChildFocusableWindowState(child);
            }
        }
    }
    
    synchronized void postWindowEvent(int id) {
        if (windowListener != null || (eventMask & AWTEvent.WINDOW_EVENT_MASK) != 0 || Toolkit.enabledOnToolkit(AWTEvent.WINDOW_EVENT_MASK)) {
            WindowEvent e = new WindowEvent(this, id);
            Toolkit.getEventQueue().postEvent(e);
        }
    }
    
    
    public void hide() {
        synchronized (ownedWindowList) {
            for (int i = 0; i < ownedWindowList.size(); i++) {
                Window child = (Window)((WeakReference)ownedWindowList.elementAt(i)).get();
                if ((child != null) && child.visible) {
                    child.hide();
                    child.showWithParent = true;
                }
            }
        }
        super.hide();
    }
    
    final void clearMostRecentFocusOwnerOnHide() {
    }
    
    public void dispose() {
        doDispose();
    }
    
    void disposeImpl() {
        dispose();
        if (getPeer() != null) {
            doDispose();
        }
    }
    
    void doDispose() {
        {
        }
        Window$1DisposeAction action = new Window$1DisposeAction(this);
        if (EventQueue.isDispatchThread()) {
            action.run();
        } else {
            try {
                EventQueue.invokeAndWait(action);
            } catch (InterruptedException e) {
                System.err.println("Disposal was interrupted:");
                e.printStackTrace();
            } catch (InvocationTargetException e) {
                System.err.println("Exception during disposal:");
                e.printStackTrace();
            }
        }
        postWindowEvent(WindowEvent.WINDOW_CLOSED);
    }
    
    void adjustListeningChildrenOnParent(long mask, int num) {
    }
    
    void adjustDecendantsOnParent(int num) {
    }
    
    public void toFront() {
        if (visible) {
            WindowPeer peer = (WindowPeer)(WindowPeer)this.peer;
            if (peer != null) {
                peer.toFront();
            }
        }
    }
    
    public void toBack() {
        if (visible) {
            WindowPeer peer = (WindowPeer)(WindowPeer)this.peer;
            if (peer != null) {
                peer.toBack();
            }
        }
    }
    
    public Toolkit getToolkit() {
        return Toolkit.getDefaultToolkit();
    }
    
    public final String getWarningString() {
        return warningString;
    }
    
    private void setWarningString() {
        warningString = null;
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            if (!sm.checkTopLevelWindow(this)) {
                warningString = (String)(String)AccessController.doPrivileged(new GetPropertyAction("awt.appletWarning", "Java Applet Window"));
            }
        }
    }
    
    public Locale getLocale() {
        if (this.locale == null) {
            return Locale.getDefault();
        }
        return this.locale;
    }
    
    public InputContext getInputContext() {
        if (inputContext == null) {
            synchronized (inputContextLock) {
                if (inputContext == null) {
                    inputContext = InputContext.getInstance();
                }
            }
        }
        return inputContext;
    }
    
    public void setCursor(Cursor cursor) {
        if (cursor == null) {
            cursor = Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR);
        }
        super.setCursor(cursor);
    }
    
    public Window getOwner() {
        return (Window)(Window)parent;
    }
    
    public Window[] getOwnedWindows() {
        Window[] realCopy;
        synchronized (ownedWindowList) {
            int fullSize = ownedWindowList.size();
            int realSize = 0;
            Window[] fullCopy = new Window[fullSize];
            for (int i = 0; i < fullSize; i++) {
                fullCopy[realSize] = (Window)((WeakReference)ownedWindowList.elementAt(i)).get();
                if (fullCopy[realSize] != null) {
                    realSize++;
                }
            }
            if (fullSize != realSize) {
                realCopy = new Window[realSize];
                System.arraycopy(fullCopy, 0, realCopy, 0, realSize);
            } else {
                realCopy = fullCopy;
            }
        }
        return realCopy;
    }
    
    public synchronized void addWindowListener(WindowListener l) {
        if (l == null) {
            return;
        }
        newEventsOnly = true;
        windowListener = AWTEventMulticaster.add(windowListener, l);
    }
    
    public synchronized void addWindowStateListener(WindowStateListener l) {
        if (l == null) {
            return;
        }
        windowStateListener = AWTEventMulticaster.add(windowStateListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void addWindowFocusListener(WindowFocusListener l) {
        if (l == null) {
            return;
        }
        windowFocusListener = AWTEventMulticaster.add(windowFocusListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void removeWindowListener(WindowListener l) {
        if (l == null) {
            return;
        }
        windowListener = AWTEventMulticaster.remove(windowListener, l);
    }
    
    public synchronized void removeWindowStateListener(WindowStateListener l) {
        if (l == null) {
            return;
        }
        windowStateListener = AWTEventMulticaster.remove(windowStateListener, l);
    }
    
    public synchronized void removeWindowFocusListener(WindowFocusListener l) {
        if (l == null) {
            return;
        }
        windowFocusListener = AWTEventMulticaster.remove(windowFocusListener, l);
    }
    
    public synchronized WindowListener[] getWindowListeners() {
        return (WindowListener[])((WindowListener[])getListeners(WindowListener.class));
    }
    
    public synchronized WindowFocusListener[] getWindowFocusListeners() {
        return (WindowFocusListener[])((WindowFocusListener[])getListeners(WindowFocusListener.class));
    }
    
    public synchronized WindowStateListener[] getWindowStateListeners() {
        return (WindowStateListener[])((WindowStateListener[])getListeners(WindowStateListener.class));
    }
    
    public EventListener[] getListeners(Class listenerType) {
        EventListener l = null;
        if (listenerType == WindowFocusListener.class) {
            l = windowFocusListener;
        } else if (listenerType == WindowStateListener.class) {
            l = windowStateListener;
        } else if (listenerType == WindowListener.class) {
            l = windowListener;
        } else {
            return super.getListeners(listenerType);
        }
        return AWTEventMulticaster.getListeners(l, listenerType);
    }
    
    boolean eventEnabled(AWTEvent e) {
        switch (e.id) {
        case WindowEvent.WINDOW_OPENED: 
        
        case WindowEvent.WINDOW_CLOSING: 
        
        case WindowEvent.WINDOW_CLOSED: 
        
        case WindowEvent.WINDOW_ICONIFIED: 
        
        case WindowEvent.WINDOW_DEICONIFIED: 
        
        case WindowEvent.WINDOW_ACTIVATED: 
        
        case WindowEvent.WINDOW_DEACTIVATED: 
            if ((eventMask & AWTEvent.WINDOW_EVENT_MASK) != 0 || windowListener != null) {
                return true;
            }
            return false;
        
        case WindowEvent.WINDOW_GAINED_FOCUS: 
        
        case WindowEvent.WINDOW_LOST_FOCUS: 
            if ((eventMask & AWTEvent.WINDOW_FOCUS_EVENT_MASK) != 0 || windowFocusListener != null) {
                return true;
            }
            return false;
        
        case WindowEvent.WINDOW_STATE_CHANGED: 
            if ((eventMask & AWTEvent.WINDOW_STATE_EVENT_MASK) != 0 || windowStateListener != null) {
                return true;
            }
            return false;
        
        default: 
            break;
        
        }
        return super.eventEnabled(e);
    }
    
    protected void processEvent(AWTEvent e) {
        if (e instanceof WindowEvent) {
            switch (e.getID()) {
            case WindowEvent.WINDOW_OPENED: 
            
            case WindowEvent.WINDOW_CLOSING: 
            
            case WindowEvent.WINDOW_CLOSED: 
            
            case WindowEvent.WINDOW_ICONIFIED: 
            
            case WindowEvent.WINDOW_DEICONIFIED: 
            
            case WindowEvent.WINDOW_ACTIVATED: 
            
            case WindowEvent.WINDOW_DEACTIVATED: 
                processWindowEvent((WindowEvent)(WindowEvent)e);
                break;
            
            case WindowEvent.WINDOW_GAINED_FOCUS: 
            
            case WindowEvent.WINDOW_LOST_FOCUS: 
                processWindowFocusEvent((WindowEvent)(WindowEvent)e);
                break;
            
            case WindowEvent.WINDOW_STATE_CHANGED: 
                processWindowStateEvent((WindowEvent)(WindowEvent)e);
            
            default: 
                break;
            
            }
            return;
        }
        super.processEvent(e);
    }
    
    protected void processWindowEvent(WindowEvent e) {
        WindowListener listener = windowListener;
        if (listener != null) {
            switch (e.getID()) {
            case WindowEvent.WINDOW_OPENED: 
                listener.windowOpened(e);
                break;
            
            case WindowEvent.WINDOW_CLOSING: 
                listener.windowClosing(e);
                break;
            
            case WindowEvent.WINDOW_CLOSED: 
                listener.windowClosed(e);
                break;
            
            case WindowEvent.WINDOW_ICONIFIED: 
                listener.windowIconified(e);
                break;
            
            case WindowEvent.WINDOW_DEICONIFIED: 
                listener.windowDeiconified(e);
                break;
            
            case WindowEvent.WINDOW_ACTIVATED: 
                listener.windowActivated(e);
                break;
            
            case WindowEvent.WINDOW_DEACTIVATED: 
                listener.windowDeactivated(e);
                break;
            
            default: 
                break;
            
            }
        }
    }
    
    protected void processWindowFocusEvent(WindowEvent e) {
        WindowFocusListener listener = windowFocusListener;
        if (listener != null) {
            switch (e.getID()) {
            case WindowEvent.WINDOW_GAINED_FOCUS: 
                listener.windowGainedFocus(e);
                break;
            
            case WindowEvent.WINDOW_LOST_FOCUS: 
                listener.windowLostFocus(e);
                break;
            
            default: 
                break;
            
            }
        }
    }
    
    protected void processWindowStateEvent(WindowEvent e) {
        WindowStateListener listener = windowStateListener;
        if (listener != null) {
            switch (e.getID()) {
            case WindowEvent.WINDOW_STATE_CHANGED: 
                listener.windowStateChanged(e);
                break;
            
            default: 
                break;
            
            }
        }
    }
    
    void preProcessKeyEvent(KeyEvent e) {
        if (e.isActionKey() && e.getKeyCode() == KeyEvent.VK_F1 && e.isControlDown() && e.isShiftDown() && e.getID() == KeyEvent.KEY_PRESSED) {
            list(System.out, 0);
        }
    }
    
    void postProcessKeyEvent(KeyEvent e) {
    }
    
    public final void setAlwaysOnTop(boolean alwaysOnTop) throws SecurityException {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.SET_WINDOW_ALWAYS_ON_TOP_PERMISSION);
        }
        boolean oldAlwaysOnTop;
        synchronized (this) {
            oldAlwaysOnTop = this.alwaysOnTop;
            this.alwaysOnTop = alwaysOnTop;
        }
        if (oldAlwaysOnTop != alwaysOnTop) {
            WindowPeer peer = (WindowPeer)(WindowPeer)this.peer;
            synchronized (getTreeLock()) {
                if (peer != null) {
                    peer.updateAlwaysOnTop();
                }
            }
            firePropertyChange("alwaysOnTop", oldAlwaysOnTop, alwaysOnTop);
        }
    }
    
    public final boolean isAlwaysOnTop() {
        return alwaysOnTop;
    }
    
    public Component getFocusOwner() {
        return (isFocused()) ? KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner() : null;
    }
    
    public Component getMostRecentFocusOwner() {
        if (isFocused()) {
            return getFocusOwner();
        } else {
            Component mostRecent = KeyboardFocusManager.getMostRecentFocusOwner(this);
            if (mostRecent != null) {
                return mostRecent;
            } else {
                return (isFocusableWindow()) ? getFocusTraversalPolicy().getInitialComponent(this) : null;
            }
        }
    }
    
    public boolean isActive() {
        return (KeyboardFocusManager.getCurrentKeyboardFocusManager().getActiveWindow() == this);
    }
    
    public boolean isFocused() {
        return (KeyboardFocusManager.getCurrentKeyboardFocusManager().getGlobalFocusedWindow() == this);
    }
    
    public Set getFocusTraversalKeys(int id) {
        if (id < 0 || id >= KeyboardFocusManager.TRAVERSAL_KEY_LENGTH) {
            throw new IllegalArgumentException("invalid focus traversal key identifier");
        }
        Set keystrokes = (focusTraversalKeys != null) ? focusTraversalKeys[id] : null;
        if (keystrokes != null) {
            return keystrokes;
        } else {
            return KeyboardFocusManager.getCurrentKeyboardFocusManager().getDefaultFocusTraversalKeys(id);
        }
    }
    
    public final void setFocusCycleRoot(boolean focusCycleRoot) {
    }
    
    public final boolean isFocusCycleRoot() {
        return true;
    }
    
    public final Container getFocusCycleRootAncestor() {
        return null;
    }
    
    public final boolean isFocusableWindow() {
        if (!getFocusableWindowState()) {
            return false;
        }
        if (this instanceof Frame || this instanceof Dialog) {
            return true;
        }
        if (getFocusTraversalPolicy().getDefaultComponent(this) == null) {
            return false;
        }
        for (Window owner = getOwner(); owner != null; owner = owner.getOwner()) {
            if (owner instanceof Frame || owner instanceof Dialog) {
                return owner.isShowing();
            }
        }
        return false;
    }
    
    public boolean getFocusableWindowState() {
        return focusableWindowState;
    }
    
    public void setFocusableWindowState(boolean focusableWindowState) {
        boolean oldFocusableWindowState;
        synchronized (this) {
            oldFocusableWindowState = this.focusableWindowState;
            this.focusableWindowState = focusableWindowState;
        }
        WindowPeer peer = (WindowPeer)(WindowPeer)this.peer;
        if (peer != null) {
            peer.updateFocusableWindowState();
        }
        firePropertyChange("focusableWindowState", oldFocusableWindowState, focusableWindowState);
        if (oldFocusableWindowState && !focusableWindowState && isFocused()) {
            for (Window owner = (Window)(Window)getParent(); owner != null; owner = (Window)(Window)owner.getParent()) {
                Component toFocus = KeyboardFocusManager.getMostRecentFocusOwner(owner);
                if (toFocus != null && toFocus.requestFocus(false)) {
                    return;
                }
            }
            KeyboardFocusManager.getCurrentKeyboardFocusManager().clearGlobalFocusOwner();
        }
    }
    
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        super.addPropertyChangeListener(listener);
    }
    
    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        super.addPropertyChangeListener(propertyName, listener);
    }
    
    void dispatchEventImpl(AWTEvent e) {
        if (e.getID() == ComponentEvent.COMPONENT_RESIZED) {
            invalidate();
            validate();
        }
        super.dispatchEventImpl(e);
    }
    
    
    public boolean postEvent(Event e) {
        if (handleEvent(e)) {
            e.consume();
            return true;
        }
        return false;
    }
    
    public boolean isShowing() {
        return visible;
    }
    
    
    public void applyResourceBundle(ResourceBundle rb) {
        applyComponentOrientation(ComponentOrientation.getOrientation(rb));
    }
    
    
    public void applyResourceBundle(String rbName) {
        applyResourceBundle(ResourceBundle.getBundle(rbName));
    }
    
    void addOwnedWindow(WeakReference weakWindow) {
        if (weakWindow != null) {
            synchronized (ownedWindowList) {
                if (!ownedWindowList.contains(weakWindow)) {
                    ownedWindowList.addElement(weakWindow);
                }
            }
        }
    }
    
    void removeOwnedWindow(WeakReference weakWindow) {
        if (weakWindow != null) {
            ownedWindowList.removeElement(weakWindow);
        }
    }
    
    void connectOwnedWindow(Window child) {
        WeakReference weakChild = new WeakReference(child);
        child.weakThis = weakChild;
        child.parent = this;
        addOwnedWindow(weakChild);
    }
    private int windowSerializedDataVersion = 2;
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        synchronized (this) {
            focusMgr = new FocusManager();
            focusMgr.focusRoot = this;
            focusMgr.focusOwner = getMostRecentFocusOwner();
            s.defaultWriteObject();
            focusMgr = null;
            AWTEventMulticaster.save(s, windowListenerK, windowListener);
            AWTEventMulticaster.save(s, windowFocusListenerK, windowFocusListener);
            AWTEventMulticaster.save(s, windowStateListenerK, windowStateListener);
        }
        s.writeObject(null);
        synchronized (ownedWindowList) {
            for (int i = 0; i < ownedWindowList.size(); i++) {
                Window child = (Window)((WeakReference)ownedWindowList.elementAt(i)).get();
                if (child != null) {
                    s.writeObject(ownedWindowK);
                    s.writeObject(child);
                }
            }
        }
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        GraphicsEnvironment.checkHeadless();
        setWarningString();
        inputContextLock = new Object();
        visible = false;
        weakThis = new WeakReference(this);
        ObjectInputStream$GetField f = s.readFields();
        syncLWRequests = f.get("syncLWRequests", systemSyncLWRequests);
        state = f.get("state", 0);
        focusableWindowState = f.get("focusableWindowState", true);
        windowSerializedDataVersion = f.get("windowSerializedDataVersion", 1);
        locationByPlatform = f.get("locationByPlatform", locationByPlatformProp);
        focusMgr = (FocusManager)(FocusManager)f.get("focusMgr", null);
        boolean aot = f.get("alwaysOnTop", false);
        if (aot) {
            setAlwaysOnTop(aot);
        }
        ownedWindowList = new Vector();
        if (windowSerializedDataVersion < 2) {
            if (focusMgr != null) {
                if (focusMgr.focusOwner != null) {
                    KeyboardFocusManager.setMostRecentFocusOwner(this, focusMgr.focusOwner);
                }
            }
            focusableWindowState = true;
        }
        Object keyOrNull;
        while (null != (keyOrNull = s.readObject())) {
            String key = ((String)(String)keyOrNull).intern();
            if (windowListenerK == key) {
                addWindowListener((WindowListener)((WindowListener)s.readObject()));
            } else if (windowFocusListenerK == key) {
                addWindowFocusListener((WindowFocusListener)((WindowFocusListener)s.readObject()));
            } else if (windowStateListenerK == key) {
                addWindowStateListener((WindowStateListener)((WindowStateListener)s.readObject()));
            } else s.readObject();
        }
        try {
            while (null != (keyOrNull = s.readObject())) {
                String key = ((String)(String)keyOrNull).intern();
                if (ownedWindowK == key) connectOwnedWindow((Window)(Window)s.readObject()); else s.readObject();
            }
        } catch (OptionalDataException e) {
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Window$AccessibleAWTWindow(this);
        }
        return accessibleContext;
    }
    {
    }
    
    public GraphicsConfiguration getGraphicsConfiguration() {
        synchronized (getTreeLock()) {
            if (graphicsConfig == null && !GraphicsEnvironment.isHeadless()) {
                graphicsConfig = GraphicsEnvironment.getLocalGraphicsEnvironment().getDefaultScreenDevice().getDefaultConfiguration();
            }
            return graphicsConfig;
        }
    }
    
    void resetGC() {
        if (!GraphicsEnvironment.isHeadless()) {
            setGCFromPeer();
            if (graphicsConfig == null) {
                graphicsConfig = GraphicsEnvironment.getLocalGraphicsEnvironment().getDefaultScreenDevice().getDefaultConfiguration();
            }
            if (dbg.on) {
                dbg.println("+ Window.resetGC(): new GC is \n+ " + graphicsConfig + "\n+ this is " + this);
            }
        }
    }
    
    public void setLocationRelativeTo(Component c) {
        Container root = null;
        if (c != null) {
            if (c instanceof Window || c instanceof Applet) {
                root = (Container)(Container)c;
            } else {
                Container parent;
                for (parent = c.getParent(); parent != null; parent = parent.getParent()) {
                    if (parent instanceof Window || parent instanceof Applet) {
                        root = parent;
                        break;
                    }
                }
            }
        }
        if ((c != null && !c.isShowing()) || root == null || !root.isShowing()) {
            Dimension paneSize = getSize();
            Dimension screenSize = getToolkit().getScreenSize();
            setLocation((screenSize.width - paneSize.width) / 2, (screenSize.height - paneSize.height) / 2);
        } else {
            Dimension invokerSize = c.getSize();
            Point invokerScreenLocation = c.getLocationOnScreen();
            Rectangle windowBounds = getBounds();
            int dx = invokerScreenLocation.x + ((invokerSize.width - windowBounds.width) >> 1);
            int dy = invokerScreenLocation.y + ((invokerSize.height - windowBounds.height) >> 1);
            Rectangle ss = root.getGraphicsConfiguration().getBounds();
            if (dy + windowBounds.height > ss.height) {
                dy = ss.height - windowBounds.height;
                if (invokerScreenLocation.x - ss.x + invokerSize.width / 2 < ss.width / 2) {
                    dx = invokerScreenLocation.x + invokerSize.width;
                } else {
                    dx = invokerScreenLocation.x - windowBounds.width;
                }
            }
            if (dx + windowBounds.width > ss.x + ss.width) {
                dx = ss.x + ss.width - windowBounds.width;
            }
            if (dx < ss.x) dx = 0;
            if (dy < ss.y) dy = 0;
            setLocation(dx, dy);
        }
    }
    
    void deliverMouseWheelToAncestor(MouseWheelEvent e) {
    }
    
    boolean dispatchMouseWheelToAncestor(MouseWheelEvent e) {
        return false;
    }
    
    public void createBufferStrategy(int numBuffers) {
        super.createBufferStrategy(numBuffers);
    }
    
    public void createBufferStrategy(int numBuffers, BufferCapabilities caps) throws AWTException {
        super.createBufferStrategy(numBuffers, caps);
    }
    
    public BufferStrategy getBufferStrategy() {
        return super.getBufferStrategy();
    }
    
    Component getTemporaryLostComponent() {
        return temporaryLostComponent;
    }
    
    Component setTemporaryLostComponent(Component component) {
        Component previousComp = temporaryLostComponent;
        if (component == null || (component.isDisplayable() && component.isVisible() && component.isEnabled() && component.isFocusable())) {
            temporaryLostComponent = component;
        } else {
            temporaryLostComponent = null;
        }
        return previousComp;
    }
    
    boolean canContainFocusOwner(Component focusOwnerCandidate) {
        return super.canContainFocusOwner(focusOwnerCandidate) && isFocusableWindow();
    }
    private boolean locationByPlatform = locationByPlatformProp;
    
    public void setLocationByPlatform(boolean locationByPlatform) {
        synchronized (getTreeLock()) {
            if (locationByPlatform && isShowing()) {
                throw new IllegalComponentStateException("The window is showing on screen.");
            }
            this.locationByPlatform = locationByPlatform;
        }
    }
    
    public boolean isLocationByPlatform() {
        synchronized (getTreeLock()) {
            return locationByPlatform;
        }
    }
    
    public void setBounds(int x, int y, int width, int height) {
        synchronized (getTreeLock()) {
            if (getBoundsOp() == ComponentPeer.SET_LOCATION || getBoundsOp() == ComponentPeer.SET_BOUNDS) {
                locationByPlatform = false;
            }
            super.setBounds(x, y, width, height);
        }
    }
}
