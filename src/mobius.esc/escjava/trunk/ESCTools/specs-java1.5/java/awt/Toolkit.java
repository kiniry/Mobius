package java.awt;

import java.util.MissingResourceException;
import java.util.Properties;
import java.util.ResourceBundle;
import java.util.StringTokenizer;
import java.awt.event.*;
import java.awt.peer.*;
import java.awt.*;
import java.awt.im.InputMethodHighlight;
import java.awt.image.ImageObserver;
import java.awt.image.ImageProducer;
import java.awt.image.ColorModel;
import java.awt.datatransfer.Clipboard;
import java.awt.dnd.DragSource;
import java.awt.dnd.DragGestureRecognizer;
import java.awt.dnd.DragGestureEvent;
import java.awt.dnd.DragGestureListener;
import java.awt.dnd.InvalidDnDOperationException;
import java.awt.dnd.peer.DragSourceContextPeer;
import java.net.URL;
import java.io.File;
import java.util.EventListener;
import java.util.Map;
import java.util.HashMap;
import java.util.WeakHashMap;
import java.util.ArrayList;
import java.beans.PropertyChangeListener;
import java.beans.PropertyChangeSupport;
import sun.awt.DebugHelper;
import sun.awt.HeadlessToolkit;
import sun.awt.NullComponentPeer;
import sun.security.util.SecurityConstants;

public abstract class Toolkit {
    
    /*synthetic*/ static ResourceBundle access$102(ResourceBundle x0) {
        return resources = x0;
    }
    
    /*synthetic*/ static Toolkit access$002(Toolkit x0) {
        return toolkit = x0;
    }
    
    /*synthetic*/ static Toolkit access$000() {
        return toolkit;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !Toolkit.class.desiredAssertionStatus();
    
    public Toolkit() {
        
    }
    
    protected abstract ButtonPeer createButton(Button target) throws HeadlessException;
    
    protected abstract TextFieldPeer createTextField(TextField target) throws HeadlessException;
    
    protected abstract LabelPeer createLabel(Label target) throws HeadlessException;
    
    protected abstract ListPeer createList(java.awt.List target) throws HeadlessException;
    
    protected abstract CheckboxPeer createCheckbox(Checkbox target) throws HeadlessException;
    
    protected abstract ScrollbarPeer createScrollbar(Scrollbar target) throws HeadlessException;
    
    protected abstract ScrollPanePeer createScrollPane(ScrollPane target) throws HeadlessException;
    
    protected abstract TextAreaPeer createTextArea(TextArea target) throws HeadlessException;
    
    protected abstract ChoicePeer createChoice(Choice target) throws HeadlessException;
    
    protected abstract FramePeer createFrame(Frame target) throws HeadlessException;
    
    protected abstract CanvasPeer createCanvas(Canvas target);
    
    protected abstract PanelPeer createPanel(Panel target);
    
    protected abstract WindowPeer createWindow(Window target) throws HeadlessException;
    
    protected abstract DialogPeer createDialog(Dialog target) throws HeadlessException;
    
    protected abstract MenuBarPeer createMenuBar(MenuBar target) throws HeadlessException;
    
    protected abstract MenuPeer createMenu(Menu target) throws HeadlessException;
    
    protected abstract PopupMenuPeer createPopupMenu(PopupMenu target) throws HeadlessException;
    
    protected abstract MenuItemPeer createMenuItem(MenuItem target) throws HeadlessException;
    
    protected abstract FileDialogPeer createFileDialog(FileDialog target) throws HeadlessException;
    
    protected abstract CheckboxMenuItemPeer createCheckboxMenuItem(CheckboxMenuItem target) throws HeadlessException;
    
    protected MouseInfoPeer getMouseInfoPeer() {
        throw new UnsupportedOperationException("Not implemented");
    }
    private static LightweightPeer lightweightMarker;
    
    protected LightweightPeer createComponent(Component target) {
        if (lightweightMarker == null) {
            lightweightMarker = new NullComponentPeer();
        }
        return lightweightMarker;
    }
    
    
    protected abstract FontPeer getFontPeer(String name, int style);
    
    protected void loadSystemColors(int[] systemColors) throws HeadlessException {
    }
    
    public void setDynamicLayout(boolean dynamic) throws HeadlessException {
    }
    
    protected boolean isDynamicLayoutSet() throws HeadlessException {
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().isDynamicLayoutSet();
        } else {
            return false;
        }
    }
    
    public boolean isDynamicLayoutActive() throws HeadlessException {
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().isDynamicLayoutActive();
        } else {
            return false;
        }
    }
    
    public abstract Dimension getScreenSize() throws HeadlessException;
    
    public abstract int getScreenResolution() throws HeadlessException;
    
    public Insets getScreenInsets(GraphicsConfiguration gc) throws HeadlessException {
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().getScreenInsets(gc);
        } else {
            return new Insets(0, 0, 0, 0);
        }
    }
    
    public abstract ColorModel getColorModel() throws HeadlessException;
    
    
    public abstract String[] getFontList();
    
    
    public abstract FontMetrics getFontMetrics(Font font);
    
    public abstract void sync();
    private static Toolkit toolkit;
    private static String atNames;
    
    private static void initAssistiveTechnologies() {
        final String sep = File.separator;
        final Properties properties = new Properties();
        atNames = (String)(String)java.security.AccessController.doPrivileged(new Toolkit$1(sep, properties));
    }
    
    private static void loadAssistiveTechnologies() {
        if (atNames != null) {
            ClassLoader cl = ClassLoader.getSystemClassLoader();
            StringTokenizer parser = new StringTokenizer(atNames, " ,");
            String atName;
            while (parser.hasMoreTokens()) {
                atName = parser.nextToken();
                try {
                    Class clazz;
                    if (cl != null) {
                        clazz = cl.loadClass(atName);
                    } else {
                        clazz = Class.forName(atName);
                    }
                    clazz.newInstance();
                } catch (ClassNotFoundException e) {
                    throw new AWTError("Assistive Technology not found: " + atName);
                } catch (InstantiationException e) {
                    throw new AWTError("Could not instantiate Assistive" + " Technology: " + atName);
                } catch (IllegalAccessException e) {
                    throw new AWTError("Could not access Assistive" + " Technology: " + atName);
                } catch (Exception e) {
                    throw new AWTError("Error trying to install Assistive" + " Technology: " + atName + " " + e);
                }
            }
        }
    }
    
    public static synchronized Toolkit getDefaultToolkit() {
        if (toolkit == null) {
            try {
                java.lang.Compiler.disable();
                java.security.AccessController.doPrivileged(new Toolkit$2());
                loadAssistiveTechnologies();
            } finally {
                java.lang.Compiler.enable();
            }
        }
        return toolkit;
    }
    
    public abstract Image getImage(String filename);
    
    public abstract Image getImage(URL url);
    
    public abstract Image createImage(String filename);
    
    public abstract Image createImage(URL url);
    
    public abstract boolean prepareImage(Image image, int width, int height, ImageObserver observer);
    
    public abstract int checkImage(Image image, int width, int height, ImageObserver observer);
    
    public abstract Image createImage(ImageProducer producer);
    
    public Image createImage(byte[] imagedata) {
        return createImage(imagedata, 0, imagedata.length);
    }
    
    public abstract Image createImage(byte[] imagedata, int imageoffset, int imagelength);
    
    public abstract PrintJob getPrintJob(Frame frame, String jobtitle, Properties props);
    
    public PrintJob getPrintJob(Frame frame, String jobtitle, JobAttributes jobAttributes, PageAttributes pageAttributes) {
        if (GraphicsEnvironment.isHeadless()) {
            throw new IllegalArgumentException();
        }
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().getPrintJob(frame, jobtitle, jobAttributes, pageAttributes);
        } else {
            return getPrintJob(frame, jobtitle, null);
        }
    }
    
    public abstract void beep();
    
    public abstract Clipboard getSystemClipboard() throws HeadlessException;
    
    public Clipboard getSystemSelection() throws HeadlessException {
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().getSystemSelection();
        } else {
            GraphicsEnvironment.checkHeadless();
            return null;
        }
    }
    
    public int getMenuShortcutKeyMask() throws HeadlessException {
        return Event.CTRL_MASK;
    }
    
    public boolean getLockingKeyState(int keyCode) throws UnsupportedOperationException {
        if (!(keyCode == KeyEvent.VK_CAPS_LOCK || keyCode == KeyEvent.VK_NUM_LOCK || keyCode == KeyEvent.VK_SCROLL_LOCK || keyCode == KeyEvent.VK_KANA_LOCK)) {
            throw new IllegalArgumentException("invalid key for Toolkit.getLockingKeyState");
        }
        throw new UnsupportedOperationException("Toolkit.getLockingKeyState");
    }
    
    public void setLockingKeyState(int keyCode, boolean on) throws UnsupportedOperationException {
        if (!(keyCode == KeyEvent.VK_CAPS_LOCK || keyCode == KeyEvent.VK_NUM_LOCK || keyCode == KeyEvent.VK_SCROLL_LOCK || keyCode == KeyEvent.VK_KANA_LOCK)) {
            throw new IllegalArgumentException("invalid key for Toolkit.setLockingKeyState");
        }
        throw new UnsupportedOperationException("Toolkit.setLockingKeyState");
    }
    
    protected static Container getNativeContainer(Component c) {
        return c.getNativeContainer();
    }
    
    public Cursor createCustomCursor(Image cursor, Point hotSpot, String name) throws IndexOutOfBoundsException, HeadlessException {
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().createCustomCursor(cursor, hotSpot, name);
        } else {
            return new Cursor(Cursor.DEFAULT_CURSOR);
        }
    }
    
    public Dimension getBestCursorSize(int preferredWidth, int preferredHeight) throws HeadlessException {
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().getBestCursorSize(preferredWidth, preferredHeight);
        } else {
            return new Dimension(0, 0);
        }
    }
    
    public int getMaximumCursorColors() throws HeadlessException {
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().getMaximumCursorColors();
        } else {
            return 0;
        }
    }
    
    public boolean isFrameStateSupported(int state) throws HeadlessException {
        if (this != Toolkit.getDefaultToolkit()) {
            return Toolkit.getDefaultToolkit().isFrameStateSupported(state);
        } else {
            return (state == Frame.NORMAL);
        }
    }
    private static ResourceBundle resources;
    
    private static native void initIDs();
    private static boolean loaded = false;
    
    static void loadLibraries() {
        if (!loaded) {
            java.security.AccessController.doPrivileged(new sun.security.action.LoadLibraryAction("awt"));
            loaded = true;
        }
    }
    static {
        java.security.AccessController.doPrivileged(new Toolkit$3());
        loadLibraries();
        initAssistiveTechnologies();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    public static String getProperty(String key, String defaultValue) {
        if (resources != null) {
            try {
                return resources.getString(key);
            } catch (MissingResourceException e) {
            }
        }
        return defaultValue;
    }
    
    public final EventQueue getSystemEventQueue() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkAwtEventQueueAccess();
        }
        return getSystemEventQueueImpl();
    }
    
    protected abstract EventQueue getSystemEventQueueImpl();
    
    static EventQueue getEventQueue() {
        return getDefaultToolkit().getSystemEventQueueImpl();
    }
    
    public abstract DragSourceContextPeer createDragSourceContextPeer(DragGestureEvent dge) throws InvalidDnDOperationException;
    
    public DragGestureRecognizer createDragGestureRecognizer(Class abstractRecognizerClass, DragSource ds, Component c, int srcActions, DragGestureListener dgl) {
        return null;
    }
    
    public final synchronized Object getDesktopProperty(String propertyName) {
        if (this instanceof HeadlessToolkit) {
            return ((HeadlessToolkit)(HeadlessToolkit)this).getUnderlyingToolkit().getDesktopProperty(propertyName);
        }
        if (desktopProperties.isEmpty()) {
            initializeDesktopProperties();
        }
        Object value;
        if (propertyName.equals("awt.dynamicLayoutSupported")) {
            value = lazilyLoadDesktopProperty(propertyName);
            return value;
        }
        value = desktopProperties.get(propertyName);
        if (value == null) {
            value = lazilyLoadDesktopProperty(propertyName);
            if (value != null) {
                setDesktopProperty(propertyName, value);
            }
        }
        return value;
    }
    
    protected final void setDesktopProperty(String name, Object newValue) {
        if (this instanceof HeadlessToolkit) {
            ((HeadlessToolkit)(HeadlessToolkit)this).getUnderlyingToolkit().setDesktopProperty(name, newValue);
            return;
        }
        Object oldValue;
        synchronized (this) {
            oldValue = desktopProperties.get(name);
            desktopProperties.put(name, newValue);
        }
        desktopPropsSupport.firePropertyChange(name, oldValue, newValue);
    }
    
    protected Object lazilyLoadDesktopProperty(String name) {
        return null;
    }
    
    protected void initializeDesktopProperties() {
    }
    
    public synchronized void addPropertyChangeListener(String name, PropertyChangeListener pcl) {
        if (pcl == null) {
            return;
        }
        desktopPropsSupport.addPropertyChangeListener(name, pcl);
    }
    
    public synchronized void removePropertyChangeListener(String name, PropertyChangeListener pcl) {
        if (pcl == null) {
            return;
        }
        desktopPropsSupport.removePropertyChangeListener(name, pcl);
    }
    
    public PropertyChangeListener[] getPropertyChangeListeners() {
        return desktopPropsSupport.getPropertyChangeListeners();
    }
    
    public synchronized PropertyChangeListener[] getPropertyChangeListeners(String propertyName) {
        return desktopPropsSupport.getPropertyChangeListeners(propertyName);
    }
    protected final Map desktopProperties = new HashMap();
    protected final PropertyChangeSupport desktopPropsSupport = new PropertyChangeSupport(this);
    private static final DebugHelper dbg = DebugHelper.create(Toolkit.class);
    private static final int LONG_BITS = 64;
    private int[] calls = new int[LONG_BITS];
    private static volatile long enabledOnToolkitMask;
    private AWTEventListener eventListener = null;
    private WeakHashMap listener2SelectiveListener = new WeakHashMap();
    
    private static AWTEventListener deProxyAWTEventListener(AWTEventListener l) {
        AWTEventListener localL = l;
        if (localL == null) {
            return null;
        }
        if (l instanceof AWTEventListenerProxy) {
            localL = (AWTEventListener)(AWTEventListener)((AWTEventListenerProxy)(AWTEventListenerProxy)l).getListener();
        }
        return localL;
    }
    
    public void addAWTEventListener(AWTEventListener listener, long eventMask) {
        AWTEventListener localL = deProxyAWTEventListener(listener);
        if (localL == null) {
            return;
        }
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.ALL_AWT_EVENTS_PERMISSION);
        }
        synchronized (this) {
            Toolkit$SelectiveAWTEventListener selectiveListener = (Toolkit$SelectiveAWTEventListener)(Toolkit$SelectiveAWTEventListener)listener2SelectiveListener.get(localL);
            if (selectiveListener == null) {
                selectiveListener = new Toolkit$SelectiveAWTEventListener(this, localL, eventMask);
                listener2SelectiveListener.put(localL, selectiveListener);
                eventListener = Toolkit$ToolkitEventMulticaster.add(eventListener, selectiveListener);
            }
            selectiveListener.orEventMasks(eventMask);
            enabledOnToolkitMask |= eventMask;
            long mask = eventMask;
            for (int i = 0; i < LONG_BITS; i++) {
                if (mask == 0) {
                    break;
                }
                if ((mask & 1L) != 0) {
                    calls[i]++;
                }
                mask >>>= 1;
            }
        }
    }
    
    public void removeAWTEventListener(AWTEventListener listener) {
        AWTEventListener localL = deProxyAWTEventListener(listener);
        if (listener == null) {
            return;
        }
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.ALL_AWT_EVENTS_PERMISSION);
        }
        synchronized (this) {
            Toolkit$SelectiveAWTEventListener selectiveListener = (Toolkit$SelectiveAWTEventListener)(Toolkit$SelectiveAWTEventListener)listener2SelectiveListener.get(localL);
            if (selectiveListener != null) {
                listener2SelectiveListener.remove(localL);
                int[] listenerCalls = selectiveListener.getCalls();
                for (int i = 0; i < LONG_BITS; i++) {
                    calls[i] -= listenerCalls[i];
                    if (!$assertionsDisabled && !(calls[i] >= 0)) throw new AssertionError("Negative Listeners count");
                    if (calls[i] == 0) {
                        enabledOnToolkitMask &= ~(1L << i);
                    }
                }
            }
            eventListener = Toolkit$ToolkitEventMulticaster.remove(eventListener, (selectiveListener == null) ? localL : selectiveListener);
        }
    }
    
    static boolean enabledOnToolkit(long eventMask) {
        return (enabledOnToolkitMask & eventMask) != 0;
    }
    
    synchronized int countAWTEventListeners(long eventMask) {
        if (dbg.on) {
            dbg.assertion(eventMask != 0);
        }
        int ci = 0;
        for (; eventMask != 0; eventMask >>>= 1, ci++) {
        }
        ci--;
        return calls[ci];
    }
    
    public AWTEventListener[] getAWTEventListeners() {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.ALL_AWT_EVENTS_PERMISSION);
        }
        synchronized (this) {
            EventListener[] la = Toolkit$ToolkitEventMulticaster.getListeners(eventListener, AWTEventListener.class);
            AWTEventListener[] ret = new AWTEventListener[la.length];
            for (int i = 0; i < la.length; i++) {
                Toolkit$SelectiveAWTEventListener sael = (Toolkit$SelectiveAWTEventListener)(Toolkit$SelectiveAWTEventListener)la[i];
                AWTEventListener tempL = sael.getListener();
                ret[i] = new AWTEventListenerProxy(sael.getEventMask(), tempL);
            }
            return ret;
        }
    }
    
    public AWTEventListener[] getAWTEventListeners(long eventMask) {
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkPermission(SecurityConstants.ALL_AWT_EVENTS_PERMISSION);
        }
        synchronized (this) {
            EventListener[] la = Toolkit$ToolkitEventMulticaster.getListeners(eventListener, AWTEventListener.class);
            java.util.List list = new ArrayList(la.length);
            for (int i = 0; i < la.length; i++) {
                Toolkit$SelectiveAWTEventListener sael = (Toolkit$SelectiveAWTEventListener)(Toolkit$SelectiveAWTEventListener)la[i];
                if ((sael.getEventMask() & eventMask) == eventMask) {
                    list.add(new AWTEventListenerProxy(sael.getEventMask(), sael.getListener()));
                }
            }
            return (AWTEventListener[])(AWTEventListener[])list.toArray(new AWTEventListener[0]);
        }
    }
    
    void notifyAWTEventListeners(AWTEvent theEvent) {
        if (this instanceof HeadlessToolkit) {
            ((HeadlessToolkit)(HeadlessToolkit)this).getUnderlyingToolkit().notifyAWTEventListeners(theEvent);
            return;
        }
        AWTEventListener eventListener = this.eventListener;
        if (eventListener != null) {
            eventListener.eventDispatched(theEvent);
        }
    }
    {
    }
    {
    }
    
    public abstract Map mapInputMethodHighlight(InputMethodHighlight highlight) throws HeadlessException;
}
