package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.beans.*;
import java.util.Vector;
import javax.accessibility.*;
import javax.swing.plaf.PopupMenuUI;
import javax.swing.event.*;

public class JPopupMenu extends JComponent implements Accessible, MenuElement {
    private static final String uiClassID = "PopupMenuUI";
    private static final Object defaultLWPopupEnabledKey = new StringBuffer("JPopupMenu.defaultLWPopupEnabledKey");
    static boolean popupPostionFixDisabled = false;
    static {
        popupPostionFixDisabled = java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction("javax.swing.adjustPopupLocationToFit", "")).equals("false");
    }
    transient Component invoker;
    transient Popup popup;
    transient Frame frame;
    private int desiredLocationX;
    private int desiredLocationY;
    private String label = null;
    private boolean paintBorder = true;
    private Insets margin = null;
    private boolean lightWeightPopup = true;
    private SingleSelectionModel selectionModel;
    private static final Object classLock = new Object();
    private static final boolean TRACE = false;
    private static final boolean VERBOSE = false;
    private static final boolean DEBUG = false;
    
    public static void setDefaultLightWeightPopupEnabled(boolean aFlag) {
        SwingUtilities.appContextPut(defaultLWPopupEnabledKey, Boolean.valueOf(aFlag));
    }
    
    public static boolean getDefaultLightWeightPopupEnabled() {
        Boolean b = (Boolean)(Boolean)SwingUtilities.appContextGet(defaultLWPopupEnabledKey);
        if (b == null) {
            SwingUtilities.appContextPut(defaultLWPopupEnabledKey, Boolean.TRUE);
            return true;
        }
        return b.booleanValue();
    }
    
    public JPopupMenu() {
        this(null);
    }
    
    public JPopupMenu(String label) {
        
        this.label = label;
        lightWeightPopup = getDefaultLightWeightPopupEnabled();
        setSelectionModel(new DefaultSingleSelectionModel());
        enableEvents(AWTEvent.MOUSE_EVENT_MASK);
        setFocusTraversalKeysEnabled(false);
        updateUI();
    }
    
    public PopupMenuUI getUI() {
        return (PopupMenuUI)(PopupMenuUI)ui;
    }
    
    public void setUI(PopupMenuUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((PopupMenuUI)(PopupMenuUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    protected void processFocusEvent(FocusEvent evt) {
        super.processFocusEvent(evt);
    }
    
    protected void processKeyEvent(KeyEvent evt) {
        MenuSelectionManager.defaultManager().processKeyEvent(evt);
        if (evt.isConsumed()) {
            return;
        }
        super.processKeyEvent(evt);
    }
    
    public SingleSelectionModel getSelectionModel() {
        return selectionModel;
    }
    
    public void setSelectionModel(SingleSelectionModel model) {
        selectionModel = model;
    }
    
    public JMenuItem add(JMenuItem menuItem) {
        super.add(menuItem);
        return menuItem;
    }
    
    public JMenuItem add(String s) {
        return add(new JMenuItem(s));
    }
    
    public JMenuItem add(Action a) {
        JMenuItem mi = createActionComponent(a);
        mi.setAction(a);
        add(mi);
        return mi;
    }
    
    Point adjustPopupLocationToFitScreen(int xposition, int yposition) {
        Point p = new Point(xposition, yposition);
        if (popupPostionFixDisabled == true || GraphicsEnvironment.isHeadless()) return p;
        Toolkit toolkit = Toolkit.getDefaultToolkit();
        Rectangle screenBounds;
        Insets screenInsets;
        GraphicsConfiguration gc = null;
        GraphicsEnvironment ge = GraphicsEnvironment.getLocalGraphicsEnvironment();
        GraphicsDevice[] gd = ge.getScreenDevices();
        for (int i = 0; i < gd.length; i++) {
            if (gd[i].getType() == GraphicsDevice.TYPE_RASTER_SCREEN) {
                GraphicsConfiguration dgc = gd[i].getDefaultConfiguration();
                if (dgc.getBounds().contains(p)) {
                    gc = dgc;
                    break;
                }
            }
        }
        if (gc == null && getInvoker() != null) {
            gc = getInvoker().getGraphicsConfiguration();
        }
        if (gc != null) {
            screenInsets = toolkit.getScreenInsets(gc);
            screenBounds = gc.getBounds();
        } else {
            screenInsets = new Insets(0, 0, 0, 0);
            screenBounds = new Rectangle(toolkit.getScreenSize());
        }
        int scrWidth = screenBounds.width - Math.abs(screenInsets.left + screenInsets.right);
        int scrHeight = screenBounds.height - Math.abs(screenInsets.top + screenInsets.bottom);
        Dimension size;
        size = this.getPreferredSize();
        if ((p.x + size.width) > screenBounds.x + scrWidth) p.x = screenBounds.x + scrWidth - size.width;
        if ((p.y + size.height) > screenBounds.y + scrHeight) p.y = screenBounds.y + scrHeight - size.height;
        if (p.x < screenBounds.x) p.x = screenBounds.x;
        if (p.y < screenBounds.y) p.y = screenBounds.y;
        return p;
    }
    
    protected JMenuItem createActionComponent(Action a) {
        JMenuItem mi = new JPopupMenu$1(this, (String)(String)a.getValue(Action.NAME), (Icon)(Icon)a.getValue(Action.SMALL_ICON));
        mi.setHorizontalTextPosition(JButton.TRAILING);
        mi.setVerticalTextPosition(JButton.CENTER);
        mi.setEnabled(a.isEnabled());
        return mi;
    }
    
    protected PropertyChangeListener createActionChangeListener(JMenuItem b) {
        return new JPopupMenu$ActionChangedListener(this, b);
    }
    {
    }
    
    public void remove(int pos) {
        if (pos < 0) {
            throw new IllegalArgumentException("index less than zero.");
        }
        if (pos > getComponentCount() - 1) {
            throw new IllegalArgumentException("index greater than the number of items.");
        }
        super.remove(pos);
    }
    
    public void setLightWeightPopupEnabled(boolean aFlag) {
        lightWeightPopup = aFlag;
    }
    
    public boolean isLightWeightPopupEnabled() {
        return lightWeightPopup;
    }
    
    public String getLabel() {
        return label;
    }
    
    public void setLabel(String label) {
        String oldValue = this.label;
        this.label = label;
        firePropertyChange("label", oldValue, label);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldValue, label);
        }
        invalidate();
        repaint();
    }
    
    public void addSeparator() {
        add(new JPopupMenu$Separator());
    }
    
    public void insert(Action a, int index) {
        JMenuItem mi = createActionComponent(a);
        mi.setAction(a);
        insert(mi, index);
    }
    
    public void insert(Component component, int index) {
        if (index < 0) {
            throw new IllegalArgumentException("index less than zero.");
        }
        int nitems = getComponentCount();
        Vector tempItems = new Vector();
        for (int i = index; i < nitems; i++) {
            tempItems.addElement(getComponent(index));
            remove(index);
        }
        add(component);
        for (int i = 0; i < tempItems.size(); i++) {
            add((Component)(Component)tempItems.elementAt(i));
        }
    }
    
    public void addPopupMenuListener(PopupMenuListener l) {
        listenerList.add(PopupMenuListener.class, l);
    }
    
    public void removePopupMenuListener(PopupMenuListener l) {
        listenerList.remove(PopupMenuListener.class, l);
    }
    
    public PopupMenuListener[] getPopupMenuListeners() {
        return (PopupMenuListener[])(PopupMenuListener[])listenerList.getListeners(PopupMenuListener.class);
    }
    
    public void addMenuKeyListener(MenuKeyListener l) {
        listenerList.add(MenuKeyListener.class, l);
    }
    
    public void removeMenuKeyListener(MenuKeyListener l) {
        listenerList.remove(MenuKeyListener.class, l);
    }
    
    public MenuKeyListener[] getMenuKeyListeners() {
        return (MenuKeyListener[])(MenuKeyListener[])listenerList.getListeners(MenuKeyListener.class);
    }
    
    protected void firePopupMenuWillBecomeVisible() {
        Object[] listeners = listenerList.getListenerList();
        PopupMenuEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == PopupMenuListener.class) {
                if (e == null) e = new PopupMenuEvent(this);
                ((PopupMenuListener)(PopupMenuListener)listeners[i + 1]).popupMenuWillBecomeVisible(e);
            }
        }
    }
    
    protected void firePopupMenuWillBecomeInvisible() {
        Object[] listeners = listenerList.getListenerList();
        PopupMenuEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == PopupMenuListener.class) {
                if (e == null) e = new PopupMenuEvent(this);
                ((PopupMenuListener)(PopupMenuListener)listeners[i + 1]).popupMenuWillBecomeInvisible(e);
            }
        }
    }
    
    protected void firePopupMenuCanceled() {
        Object[] listeners = listenerList.getListenerList();
        PopupMenuEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == PopupMenuListener.class) {
                if (e == null) e = new PopupMenuEvent(this);
                ((PopupMenuListener)(PopupMenuListener)listeners[i + 1]).popupMenuCanceled(e);
            }
        }
    }
    
    boolean alwaysOnTop() {
        return true;
    }
    
    public void pack() {
        if (popup != null) {
            Dimension pref = getPreferredSize();
            if (pref == null || pref.width != getWidth() || pref.height != getHeight()) {
                popup = getPopup();
            } else {
                validate();
            }
        }
    }
    
    public void setVisible(boolean b) {
        ;
        if (b == isVisible()) return;
        if (b == false) {
            Boolean doCanceled = (Boolean)(Boolean)getClientProperty("JPopupMenu.firePopupMenuCanceled");
            if (doCanceled != null && doCanceled == Boolean.TRUE) {
                putClientProperty("JPopupMenu.firePopupMenuCanceled", Boolean.FALSE);
                firePopupMenuCanceled();
            }
            getSelectionModel().clearSelection();
        } else {
            if (isPopupMenu()) {
                if (getSubElements().length > 0) {
                    MenuElement[] me = new MenuElement[2];
                    me[0] = (MenuElement)this;
                    me[1] = getSubElements()[0];
                    MenuSelectionManager.defaultManager().setSelectedPath(me);
                } else {
                    MenuElement[] me = new MenuElement[1];
                    me[0] = (MenuElement)this;
                    MenuSelectionManager.defaultManager().setSelectedPath(me);
                }
            }
        }
        if (b) {
            firePopupMenuWillBecomeVisible();
            popup = getPopup();
            firePropertyChange("visible", Boolean.FALSE, Boolean.TRUE);
        } else if (popup != null) {
            firePopupMenuWillBecomeInvisible();
            popup.hide();
            popup = null;
            firePropertyChange("visible", Boolean.TRUE, Boolean.FALSE);
            if (isPopupMenu()) {
                MenuSelectionManager.defaultManager().clearSelectedPath();
            }
        }
    }
    
    private Popup getPopup() {
        Popup oldPopup = popup;
        if (oldPopup != null) {
            oldPopup.hide();
        }
        PopupFactory popupFactory = PopupFactory.getSharedInstance();
        if (isLightWeightPopupEnabled()) {
            popupFactory.setPopupType(PopupFactory.LIGHT_WEIGHT_POPUP);
        } else {
            popupFactory.setPopupType(PopupFactory.MEDIUM_WEIGHT_POPUP);
        }
        Point p = adjustPopupLocationToFitScreen(desiredLocationX, desiredLocationY);
        desiredLocationX = p.x;
        desiredLocationY = p.y;
        Popup newPopup = getUI().getPopup(this, desiredLocationX, desiredLocationY);
        popupFactory.setPopupType(PopupFactory.LIGHT_WEIGHT_POPUP);
        newPopup.show();
        return newPopup;
    }
    
    public boolean isVisible() {
        if (popup != null) return true; else return false;
    }
    
    public void setLocation(int x, int y) {
        int oldX = desiredLocationX;
        int oldY = desiredLocationY;
        desiredLocationX = x;
        desiredLocationY = y;
        if (popup != null && (x != oldX || y != oldY)) {
            popup = getPopup();
        }
    }
    
    private boolean isPopupMenu() {
        return ((invoker != null) && !(invoker instanceof JMenu));
    }
    
    public Component getInvoker() {
        return this.invoker;
    }
    
    public void setInvoker(Component invoker) {
        Component oldInvoker = this.invoker;
        this.invoker = invoker;
        if ((oldInvoker != this.invoker) && (ui != null)) {
            ui.uninstallUI(this);
            ui.installUI(this);
        }
        invalidate();
    }
    
    public void show(Component invoker, int x, int y) {
        ;
        setInvoker(invoker);
        Frame newFrame = getFrame(invoker);
        if (newFrame != frame) {
            if (newFrame != null) {
                this.frame = newFrame;
                if (popup != null) {
                    setVisible(false);
                }
            }
        }
        Point invokerOrigin;
        if (invoker != null) {
            invokerOrigin = invoker.getLocationOnScreen();
            setLocation(invokerOrigin.x + x, invokerOrigin.y + y);
        } else {
            setLocation(x, y);
        }
        setVisible(true);
    }
    
    JPopupMenu getRootPopupMenu() {
        JPopupMenu mp = this;
        while ((mp != null) && (mp.isPopupMenu() != true) && (mp.getInvoker() != null) && (mp.getInvoker().getParent() != null) && (mp.getInvoker().getParent() instanceof JPopupMenu)) {
            mp = (JPopupMenu)(JPopupMenu)mp.getInvoker().getParent();
        }
        return mp;
    }
    
    
    public Component getComponentAtIndex(int i) {
        return getComponent(i);
    }
    
    public int getComponentIndex(Component c) {
        int ncomponents = this.getComponentCount();
        Component[] component = this.getComponents();
        for (int i = 0; i < ncomponents; i++) {
            Component comp = component[i];
            if (comp == c) return i;
        }
        return -1;
    }
    
    public void setPopupSize(Dimension d) {
        Dimension oldSize = getPreferredSize();
        setPreferredSize(d);
        if (popup != null) {
            Dimension newSize = getPreferredSize();
            if (!oldSize.equals(newSize)) {
                popup = getPopup();
            }
        }
    }
    
    public void setPopupSize(int width, int height) {
        setPopupSize(new Dimension(width, height));
    }
    
    public void setSelected(Component sel) {
        SingleSelectionModel model = getSelectionModel();
        int index = getComponentIndex(sel);
        model.setSelectedIndex(index);
    }
    
    public boolean isBorderPainted() {
        return paintBorder;
    }
    
    public void setBorderPainted(boolean b) {
        paintBorder = b;
        repaint();
    }
    
    protected void paintBorder(Graphics g) {
        if (isBorderPainted()) {
            super.paintBorder(g);
        }
    }
    
    public Insets getMargin() {
        if (margin == null) {
            return new Insets(0, 0, 0, 0);
        } else {
            return margin;
        }
    }
    
    boolean isSubPopupMenu(JPopupMenu popup) {
        int ncomponents = this.getComponentCount();
        Component[] component = this.getComponents();
        for (int i = 0; i < ncomponents; i++) {
            Component comp = component[i];
            if (comp instanceof JMenu) {
                JMenu menu = (JMenu)(JMenu)comp;
                JPopupMenu subPopup = menu.getPopupMenu();
                if (subPopup == popup) return true;
                if (subPopup.isSubPopupMenu(popup)) return true;
            }
        }
        return false;
    }
    
    private static Frame getFrame(Component c) {
        Component w = c;
        while (!(w instanceof Frame) && (w != null)) {
            w = w.getParent();
        }
        return (Frame)(Frame)w;
    }
    
    protected String paramString() {
        String labelString = (label != null ? label : "");
        String paintBorderString = (paintBorder ? "true" : "false");
        String marginString = (margin != null ? margin.toString() : "");
        String lightWeightPopupEnabledString = (isLightWeightPopupEnabled() ? "true" : "false");
        return super.paramString() + ",desiredLocationX=" + desiredLocationX + ",desiredLocationY=" + desiredLocationY + ",label=" + labelString + ",lightWeightPopupEnabled=" + lightWeightPopupEnabledString + ",margin=" + marginString + ",paintBorder=" + paintBorderString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JPopupMenu$AccessibleJPopupMenu(this);
        }
        return accessibleContext;
    }
    {
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        Vector values = new Vector();
        s.defaultWriteObject();
        if (invoker != null && invoker instanceof Serializable) {
            values.addElement("invoker");
            values.addElement(invoker);
        }
        if (popup != null && popup instanceof Serializable) {
            values.addElement("popup");
            values.addElement(popup);
        }
        s.writeObject(values);
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        Vector values = (Vector)(Vector)s.readObject();
        int indexCounter = 0;
        int maxCounter = values.size();
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("invoker")) {
            invoker = (Component)(Component)values.elementAt(++indexCounter);
            indexCounter++;
        }
        if (indexCounter < maxCounter && values.elementAt(indexCounter).equals("popup")) {
            popup = (Popup)(Popup)values.elementAt(++indexCounter);
            indexCounter++;
        }
    }
    
    public void processMouseEvent(MouseEvent event, MenuElement[] path, MenuSelectionManager manager) {
    }
    
    public void processKeyEvent(KeyEvent e, MenuElement[] path, MenuSelectionManager manager) {
        MenuKeyEvent mke = new MenuKeyEvent(e.getComponent(), e.getID(), e.getWhen(), e.getModifiers(), e.getKeyCode(), e.getKeyChar(), path, manager);
        processMenuKeyEvent(mke);
        if (mke.isConsumed()) {
            e.consume();
        }
    }
    
    private void processMenuKeyEvent(MenuKeyEvent e) {
        switch (e.getID()) {
        case KeyEvent.KEY_PRESSED: 
            fireMenuKeyPressed(e);
            break;
        
        case KeyEvent.KEY_RELEASED: 
            fireMenuKeyReleased(e);
            break;
        
        case KeyEvent.KEY_TYPED: 
            fireMenuKeyTyped(e);
            break;
        
        default: 
            break;
        
        }
    }
    
    private void fireMenuKeyPressed(MenuKeyEvent event) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuKeyListener.class) {
                ((MenuKeyListener)(MenuKeyListener)listeners[i + 1]).menuKeyPressed(event);
            }
        }
    }
    
    private void fireMenuKeyReleased(MenuKeyEvent event) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuKeyListener.class) {
                ((MenuKeyListener)(MenuKeyListener)listeners[i + 1]).menuKeyReleased(event);
            }
        }
    }
    
    private void fireMenuKeyTyped(MenuKeyEvent event) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuKeyListener.class) {
                ((MenuKeyListener)(MenuKeyListener)listeners[i + 1]).menuKeyTyped(event);
            }
        }
    }
    
    public void menuSelectionChanged(boolean isIncluded) {
        ;
        if (invoker instanceof JMenu) {
            JMenu m = (JMenu)(JMenu)invoker;
            if (isIncluded) m.setPopupMenuVisible(true); else m.setPopupMenuVisible(false);
        }
        if (isPopupMenu() && !isIncluded) setVisible(false);
    }
    
    public MenuElement[] getSubElements() {
        MenuElement[] result;
        Vector tmp = new Vector();
        int c = getComponentCount();
        int i;
        Component m;
        for (i = 0; i < c; i++) {
            m = getComponent(i);
            if (m instanceof MenuElement) tmp.addElement(m);
        }
        result = new MenuElement[tmp.size()];
        for (i = 0, c = tmp.size(); i < c; i++) result[i] = (MenuElement)(MenuElement)tmp.elementAt(i);
        return result;
    }
    
    public Component getComponent() {
        return this;
    }
    {
    }
    
    public boolean isPopupTrigger(MouseEvent e) {
        return getUI().isPopupTrigger(e);
    }
}
