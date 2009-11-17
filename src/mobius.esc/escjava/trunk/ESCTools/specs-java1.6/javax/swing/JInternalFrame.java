package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.PropertyVetoException;
import javax.swing.event.InternalFrameEvent;
import javax.swing.event.InternalFrameListener;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JInternalFrame extends JComponent implements Accessible, WindowConstants, RootPaneContainer {
    private static final String uiClassID = "InternalFrameUI";
    protected JRootPane rootPane;
    protected boolean rootPaneCheckingEnabled = false;
    protected boolean closable;
    protected boolean isClosed;
    protected boolean maximizable;
    protected boolean isMaximum;
    protected boolean iconable;
    protected boolean isIcon;
    protected boolean resizable;
    protected boolean isSelected;
    protected Icon frameIcon;
    protected String title;
    protected JInternalFrame$JDesktopIcon desktopIcon;
    private boolean opened;
    private Rectangle normalBounds = null;
    private int defaultCloseOperation = DISPOSE_ON_CLOSE;
    private Component lastFocusOwner;
    public static final String CONTENT_PANE_PROPERTY = "contentPane";
    public static final String MENU_BAR_PROPERTY = "JMenuBar";
    public static final String TITLE_PROPERTY = "title";
    public static final String LAYERED_PANE_PROPERTY = "layeredPane";
    public static final String ROOT_PANE_PROPERTY = "rootPane";
    public static final String GLASS_PANE_PROPERTY = "glassPane";
    public static final String FRAME_ICON_PROPERTY = "frameIcon";
    public static final String IS_SELECTED_PROPERTY = "selected";
    public static final String IS_CLOSED_PROPERTY = "closed";
    public static final String IS_MAXIMUM_PROPERTY = "maximum";
    public static final String IS_ICON_PROPERTY = "icon";
    
    public JInternalFrame() {
        this("", false, false, false, false);
    }
    
    public JInternalFrame(String title) {
        this(title, false, false, false, false);
    }
    
    public JInternalFrame(String title, boolean resizable) {
        this(title, resizable, false, false, false);
    }
    
    public JInternalFrame(String title, boolean resizable, boolean closable) {
        this(title, resizable, closable, false, false);
    }
    
    public JInternalFrame(String title, boolean resizable, boolean closable, boolean maximizable) {
        this(title, resizable, closable, maximizable, false);
    }
    
    public JInternalFrame(String title, boolean resizable, boolean closable, boolean maximizable, boolean iconifiable) {
        
        setRootPane(createRootPane());
        getGlassPane().setVisible(true);
        setLayout(new BorderLayout());
        this.title = title;
        this.resizable = resizable;
        this.closable = closable;
        this.maximizable = maximizable;
        isMaximum = false;
        this.iconable = iconifiable;
        isIcon = false;
        setVisible(false);
        setRootPaneCheckingEnabled(true);
        desktopIcon = new JInternalFrame$JDesktopIcon(this);
        updateUI();
        sun.awt.SunToolkit.checkAndSetPolicy(this, true);
    }
    
    protected JRootPane createRootPane() {
        return new JRootPane();
    }
    
    public InternalFrameUI getUI() {
        return (InternalFrameUI)(InternalFrameUI)ui;
    }
    
    public void setUI(InternalFrameUI ui) {
        boolean checkingEnabled = isRootPaneCheckingEnabled();
        try {
            setRootPaneCheckingEnabled(false);
            super.setUI(ui);
        } finally {
            setRootPaneCheckingEnabled(checkingEnabled);
        }
    }
    
    public void updateUI() {
        setUI((InternalFrameUI)(InternalFrameUI)UIManager.getUI(this));
        invalidate();
        if (desktopIcon != null) {
            desktopIcon.updateUIWhenHidden();
        }
    }
    
    void updateUIWhenHidden() {
        setUI((InternalFrameUI)(InternalFrameUI)UIManager.getUI(this));
        invalidate();
        Component[] children = getComponents();
        if (children != null) {
            for (int i = 0; i < children.length; i++) {
                SwingUtilities.updateComponentTreeUI(children[i]);
            }
        }
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    protected boolean isRootPaneCheckingEnabled() {
        return rootPaneCheckingEnabled;
    }
    
    protected void setRootPaneCheckingEnabled(boolean enabled) {
        rootPaneCheckingEnabled = enabled;
    }
    
    protected void addImpl(Component comp, Object constraints, int index) {
        if (isRootPaneCheckingEnabled()) {
            getContentPane().add(comp, constraints, index);
        } else {
            super.addImpl(comp, constraints, index);
        }
    }
    
    public void remove(Component comp) {
        int oldCount = getComponentCount();
        super.remove(comp);
        if (oldCount == getComponentCount()) {
            getContentPane().remove(comp);
        }
    }
    
    public void setLayout(LayoutManager manager) {
        if (isRootPaneCheckingEnabled()) {
            getContentPane().setLayout(manager);
        } else {
            super.setLayout(manager);
        }
    }
    
    
    public JMenuBar getMenuBar() {
        return getRootPane().getMenuBar();
    }
    
    public JMenuBar getJMenuBar() {
        return getRootPane().getJMenuBar();
    }
    
    
    public void setMenuBar(JMenuBar m) {
        JMenuBar oldValue = getMenuBar();
        getRootPane().setJMenuBar(m);
        firePropertyChange(MENU_BAR_PROPERTY, oldValue, m);
    }
    
    public void setJMenuBar(JMenuBar m) {
        JMenuBar oldValue = getMenuBar();
        getRootPane().setJMenuBar(m);
        firePropertyChange(MENU_BAR_PROPERTY, oldValue, m);
    }
    
    public Container getContentPane() {
        return getRootPane().getContentPane();
    }
    
    public void setContentPane(Container c) {
        Container oldValue = getContentPane();
        getRootPane().setContentPane(c);
        firePropertyChange(CONTENT_PANE_PROPERTY, oldValue, c);
    }
    
    public JLayeredPane getLayeredPane() {
        return getRootPane().getLayeredPane();
    }
    
    public void setLayeredPane(JLayeredPane layered) {
        JLayeredPane oldValue = getLayeredPane();
        getRootPane().setLayeredPane(layered);
        firePropertyChange(LAYERED_PANE_PROPERTY, oldValue, layered);
    }
    
    public Component getGlassPane() {
        return getRootPane().getGlassPane();
    }
    
    public void setGlassPane(Component glass) {
        Component oldValue = getGlassPane();
        getRootPane().setGlassPane(glass);
        firePropertyChange(GLASS_PANE_PROPERTY, oldValue, glass);
    }
    
    public JRootPane getRootPane() {
        return rootPane;
    }
    
    protected void setRootPane(JRootPane root) {
        if (rootPane != null) {
            remove(rootPane);
        }
        JRootPane oldValue = getRootPane();
        rootPane = root;
        if (rootPane != null) {
            boolean checkingEnabled = isRootPaneCheckingEnabled();
            try {
                setRootPaneCheckingEnabled(false);
                add(rootPane, BorderLayout.CENTER);
            } finally {
                setRootPaneCheckingEnabled(checkingEnabled);
            }
        }
        firePropertyChange(ROOT_PANE_PROPERTY, oldValue, root);
    }
    
    public void setClosable(boolean b) {
        Boolean oldValue = closable ? Boolean.TRUE : Boolean.FALSE;
        Boolean newValue = b ? Boolean.TRUE : Boolean.FALSE;
        closable = b;
        firePropertyChange("closable", oldValue, newValue);
    }
    
    public boolean isClosable() {
        return closable;
    }
    
    public boolean isClosed() {
        return isClosed;
    }
    
    public void setClosed(boolean b) throws PropertyVetoException {
        if (isClosed == b) {
            return;
        }
        Boolean oldValue = isClosed ? Boolean.TRUE : Boolean.FALSE;
        Boolean newValue = b ? Boolean.TRUE : Boolean.FALSE;
        if (b) {
            fireInternalFrameEvent(InternalFrameEvent.INTERNAL_FRAME_CLOSING);
        }
        fireVetoableChange(IS_CLOSED_PROPERTY, oldValue, newValue);
        isClosed = b;
        firePropertyChange(IS_CLOSED_PROPERTY, oldValue, newValue);
        if (isClosed) {
            dispose();
        } else if (!opened) {
        }
    }
    
    public void setResizable(boolean b) {
        Boolean oldValue = resizable ? Boolean.TRUE : Boolean.FALSE;
        Boolean newValue = b ? Boolean.TRUE : Boolean.FALSE;
        resizable = b;
        firePropertyChange("resizable", oldValue, newValue);
    }
    
    public boolean isResizable() {
        return isMaximum ? false : resizable;
    }
    
    public void setIconifiable(boolean b) {
        Boolean oldValue = iconable ? Boolean.TRUE : Boolean.FALSE;
        Boolean newValue = b ? Boolean.TRUE : Boolean.FALSE;
        iconable = b;
        firePropertyChange("iconable", oldValue, newValue);
    }
    
    public boolean isIconifiable() {
        return iconable;
    }
    
    public boolean isIcon() {
        return isIcon;
    }
    
    public void setIcon(boolean b) throws PropertyVetoException {
        if (isIcon == b) {
            return;
        }
        firePropertyChange("ancestor", null, getParent());
        Boolean oldValue = isIcon ? Boolean.TRUE : Boolean.FALSE;
        Boolean newValue = b ? Boolean.TRUE : Boolean.FALSE;
        fireVetoableChange(IS_ICON_PROPERTY, oldValue, newValue);
        isIcon = b;
        firePropertyChange(IS_ICON_PROPERTY, oldValue, newValue);
        if (b) fireInternalFrameEvent(InternalFrameEvent.INTERNAL_FRAME_ICONIFIED); else fireInternalFrameEvent(InternalFrameEvent.INTERNAL_FRAME_DEICONIFIED);
    }
    
    public void setMaximizable(boolean b) {
        Boolean oldValue = maximizable ? Boolean.TRUE : Boolean.FALSE;
        Boolean newValue = b ? Boolean.TRUE : Boolean.FALSE;
        maximizable = b;
        firePropertyChange("maximizable", oldValue, newValue);
    }
    
    public boolean isMaximizable() {
        return maximizable;
    }
    
    public boolean isMaximum() {
        return isMaximum;
    }
    
    public void setMaximum(boolean b) throws PropertyVetoException {
        if (isMaximum == b) {
            return;
        }
        Boolean oldValue = isMaximum ? Boolean.TRUE : Boolean.FALSE;
        Boolean newValue = b ? Boolean.TRUE : Boolean.FALSE;
        fireVetoableChange(IS_MAXIMUM_PROPERTY, oldValue, newValue);
        isMaximum = b;
        firePropertyChange(IS_MAXIMUM_PROPERTY, oldValue, newValue);
    }
    
    public String getTitle() {
        return title;
    }
    
    public void setTitle(String title) {
        String oldValue = this.title;
        this.title = title;
        firePropertyChange(TITLE_PROPERTY, oldValue, title);
    }
    
    public void setSelected(boolean selected) throws PropertyVetoException {
        if ((isSelected == selected) || (selected && (isIcon ? !desktopIcon.isShowing() : !isShowing()))) {
            return;
        }
        Boolean oldValue = isSelected ? Boolean.TRUE : Boolean.FALSE;
        Boolean newValue = selected ? Boolean.TRUE : Boolean.FALSE;
        fireVetoableChange(IS_SELECTED_PROPERTY, oldValue, newValue);
        lastFocusOwner = null;
        if (selected) {
            restoreSubcomponentFocus();
        } else {
            getRootPane().setMostRecentFocusOwner(getFocusOwner());
        }
        isSelected = selected;
        firePropertyChange(IS_SELECTED_PROPERTY, oldValue, newValue);
        if (isSelected) fireInternalFrameEvent(InternalFrameEvent.INTERNAL_FRAME_ACTIVATED); else fireInternalFrameEvent(InternalFrameEvent.INTERNAL_FRAME_DEACTIVATED);
        lastFocusOwner = null;
        repaint();
    }
    
    public boolean isSelected() {
        return isSelected;
    }
    
    public void setFrameIcon(Icon icon) {
        Icon oldIcon = frameIcon;
        frameIcon = icon;
        firePropertyChange(FRAME_ICON_PROPERTY, oldIcon, icon);
    }
    
    public Icon getFrameIcon() {
        return frameIcon;
    }
    
    public void moveToFront() {
        if (getParent() != null && getParent() instanceof JLayeredPane) {
            JLayeredPane l = (JLayeredPane)(JLayeredPane)getParent();
            Component focusOwner = (lastFocusOwner != null) ? lastFocusOwner : KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
            if (focusOwner != null && !SwingUtilities.isDescendingFrom(focusOwner, this)) {
                focusOwner = null;
            }
            l.moveToFront(this);
            if (focusOwner != null) {
                focusOwner.requestFocus();
            }
        }
    }
    
    public void moveToBack() {
        if (getParent() != null && getParent() instanceof JLayeredPane) {
            JLayeredPane l = (JLayeredPane)(JLayeredPane)getParent();
            l.moveToBack(this);
        }
    }
    
    public void setLayer(Integer layer) {
        if (getParent() != null && getParent() instanceof JLayeredPane) {
            JLayeredPane p = (JLayeredPane)(JLayeredPane)getParent();
            p.setLayer(this, layer.intValue(), p.getPosition(this));
        } else {
            JLayeredPane.putLayer(this, layer.intValue());
            if (getParent() != null) getParent().repaint(getX(), getY(), getWidth(), getHeight());
        }
    }
    
    public void setLayer(int layer) {
        this.setLayer(new Integer(layer));
    }
    
    public int getLayer() {
        return JLayeredPane.getLayer(this);
    }
    
    public JDesktopPane getDesktopPane() {
        Container p;
        p = getParent();
        while (p != null && !(p instanceof JDesktopPane)) p = p.getParent();
        if (p == null) {
            p = getDesktopIcon().getParent();
            while (p != null && !(p instanceof JDesktopPane)) p = p.getParent();
        }
        return (JDesktopPane)(JDesktopPane)p;
    }
    
    public void setDesktopIcon(JInternalFrame$JDesktopIcon d) {
        JInternalFrame$JDesktopIcon oldValue = getDesktopIcon();
        desktopIcon = d;
        firePropertyChange("desktopIcon", oldValue, d);
    }
    
    public JInternalFrame$JDesktopIcon getDesktopIcon() {
        return desktopIcon;
    }
    
    public Rectangle getNormalBounds() {
        if (normalBounds != null) {
            return normalBounds;
        } else {
            return getBounds();
        }
    }
    
    public void setNormalBounds(Rectangle r) {
        normalBounds = r;
    }
    
    public Component getFocusOwner() {
        if (isSelected()) {
            Component focusOwner = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
            if (focusOwner != null && !SwingUtilities.isDescendingFrom(focusOwner, this)) {
                focusOwner = null;
            }
            return focusOwner;
        }
        return null;
    }
    
    public Component getMostRecentFocusOwner() {
        if (isSelected()) {
            return getFocusOwner();
        }
        Component mostRecentFocusOwner = getRootPane().getMostRecentFocusOwner();
        if (mostRecentFocusOwner != null) {
            return mostRecentFocusOwner;
        }
        FocusTraversalPolicy policy = getFocusTraversalPolicy();
        if (policy instanceof InternalFrameFocusTraversalPolicy) {
            return ((InternalFrameFocusTraversalPolicy)(InternalFrameFocusTraversalPolicy)policy).getInitialComponent(this);
        }
        return policy.getDefaultComponent(this);
    }
    
    public void restoreSubcomponentFocus() {
        lastFocusOwner = getMostRecentFocusOwner();
        if (lastFocusOwner == null) {
            lastFocusOwner = getContentPane();
        }
        lastFocusOwner.requestFocus();
    }
    
    public void reshape(int x, int y, int width, int height) {
        super.reshape(x, y, width, height);
        validate();
        repaint();
    }
    
    public void addInternalFrameListener(InternalFrameListener l) {
        listenerList.add(InternalFrameListener.class, l);
        enableEvents(0);
    }
    
    public void removeInternalFrameListener(InternalFrameListener l) {
        listenerList.remove(InternalFrameListener.class, l);
    }
    
    public InternalFrameListener[] getInternalFrameListeners() {
        return (InternalFrameListener[])(InternalFrameListener[])listenerList.getListeners(InternalFrameListener.class);
    }
    
    protected void fireInternalFrameEvent(int id) {
        Object[] listeners = listenerList.getListenerList();
        InternalFrameEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == InternalFrameListener.class) {
                if (e == null) {
                    e = new InternalFrameEvent(this, id);
                }
                switch (e.getID()) {
                case InternalFrameEvent.INTERNAL_FRAME_OPENED: 
                    ((InternalFrameListener)(InternalFrameListener)listeners[i + 1]).internalFrameOpened(e);
                    break;
                
                case InternalFrameEvent.INTERNAL_FRAME_CLOSING: 
                    ((InternalFrameListener)(InternalFrameListener)listeners[i + 1]).internalFrameClosing(e);
                    break;
                
                case InternalFrameEvent.INTERNAL_FRAME_CLOSED: 
                    ((InternalFrameListener)(InternalFrameListener)listeners[i + 1]).internalFrameClosed(e);
                    break;
                
                case InternalFrameEvent.INTERNAL_FRAME_ICONIFIED: 
                    ((InternalFrameListener)(InternalFrameListener)listeners[i + 1]).internalFrameIconified(e);
                    break;
                
                case InternalFrameEvent.INTERNAL_FRAME_DEICONIFIED: 
                    ((InternalFrameListener)(InternalFrameListener)listeners[i + 1]).internalFrameDeiconified(e);
                    break;
                
                case InternalFrameEvent.INTERNAL_FRAME_ACTIVATED: 
                    ((InternalFrameListener)(InternalFrameListener)listeners[i + 1]).internalFrameActivated(e);
                    break;
                
                case InternalFrameEvent.INTERNAL_FRAME_DEACTIVATED: 
                    ((InternalFrameListener)(InternalFrameListener)listeners[i + 1]).internalFrameDeactivated(e);
                    break;
                
                default: 
                    break;
                
                }
            }
        }
    }
    
    public void doDefaultCloseAction() {
        fireInternalFrameEvent(InternalFrameEvent.INTERNAL_FRAME_CLOSING);
        switch (defaultCloseOperation) {
        case DO_NOTHING_ON_CLOSE: 
            break;
        
        case HIDE_ON_CLOSE: 
            setVisible(false);
            if (isSelected()) try {
                setSelected(false);
            } catch (PropertyVetoException pve) {
            }
            break;
        
        case DISPOSE_ON_CLOSE: 
            try {
                fireVetoableChange(IS_CLOSED_PROPERTY, Boolean.FALSE, Boolean.TRUE);
                isClosed = true;
                firePropertyChange(IS_CLOSED_PROPERTY, Boolean.FALSE, Boolean.TRUE);
                dispose();
            } catch (PropertyVetoException pve) {
            }
            break;
        
        default: 
            break;
        
        }
    }
    
    public void setDefaultCloseOperation(int operation) {
        this.defaultCloseOperation = operation;
    }
    
    public int getDefaultCloseOperation() {
        return defaultCloseOperation;
    }
    
    public void pack() {
        try {
            if (isIcon()) {
                setIcon(false);
            } else if (isMaximum()) {
                setMaximum(false);
            }
        } catch (PropertyVetoException e) {
            return;
        }
        setSize(getPreferredSize());
        validate();
    }
    
    public void show() {
        if (isVisible()) {
            return;
        }
        if (!opened) {
            fireInternalFrameEvent(InternalFrameEvent.INTERNAL_FRAME_OPENED);
            opened = true;
        }
        getDesktopIcon().setVisible(true);
        toFront();
        super.show();
        if (isIcon) {
            return;
        }
        if (!isSelected()) {
            try {
                setSelected(true);
            } catch (PropertyVetoException pve) {
            }
        }
    }
    
    public void hide() {
        if (isIcon()) {
            getDesktopIcon().setVisible(false);
        }
        super.hide();
    }
    
    public void dispose() {
        if (isVisible()) {
            setVisible(false);
        }
        if (isSelected()) {
            try {
                setSelected(false);
            } catch (PropertyVetoException pve) {
            }
        }
        if (!isClosed) {
            firePropertyChange(IS_CLOSED_PROPERTY, Boolean.FALSE, Boolean.TRUE);
            isClosed = true;
        }
        fireInternalFrameEvent(InternalFrameEvent.INTERNAL_FRAME_CLOSED);
    }
    
    public void toFront() {
        moveToFront();
    }
    
    public void toBack() {
        moveToBack();
    }
    
    public final void setFocusCycleRoot(boolean focusCycleRoot) {
    }
    
    public final boolean isFocusCycleRoot() {
        return true;
    }
    
    public final Container getFocusCycleRootAncestor() {
        return null;
    }
    
    public final String getWarningString() {
        return null;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                boolean old = isRootPaneCheckingEnabled();
                try {
                    setRootPaneCheckingEnabled(false);
                    ui.installUI(this);
                } finally {
                    setRootPaneCheckingEnabled(old);
                }
            }
        }
    }
    
    void compWriteObjectNotify() {
        boolean old = isRootPaneCheckingEnabled();
        try {
            setRootPaneCheckingEnabled(false);
            super.compWriteObjectNotify();
        } finally {
            setRootPaneCheckingEnabled(old);
        }
    }
    
    protected String paramString() {
        String rootPaneString = (rootPane != null ? rootPane.toString() : "");
        String rootPaneCheckingEnabledString = (rootPaneCheckingEnabled ? "true" : "false");
        String closableString = (closable ? "true" : "false");
        String isClosedString = (isClosed ? "true" : "false");
        String maximizableString = (maximizable ? "true" : "false");
        String isMaximumString = (isMaximum ? "true" : "false");
        String iconableString = (iconable ? "true" : "false");
        String isIconString = (isIcon ? "true" : "false");
        String resizableString = (resizable ? "true" : "false");
        String isSelectedString = (isSelected ? "true" : "false");
        String frameIconString = (frameIcon != null ? frameIcon.toString() : "");
        String titleString = (title != null ? title : "");
        String desktopIconString = (desktopIcon != null ? desktopIcon.toString() : "");
        String openedString = (opened ? "true" : "false");
        String defaultCloseOperationString;
        if (defaultCloseOperation == HIDE_ON_CLOSE) {
            defaultCloseOperationString = "HIDE_ON_CLOSE";
        } else if (defaultCloseOperation == DISPOSE_ON_CLOSE) {
            defaultCloseOperationString = "DISPOSE_ON_CLOSE";
        } else if (defaultCloseOperation == DO_NOTHING_ON_CLOSE) {
            defaultCloseOperationString = "DO_NOTHING_ON_CLOSE";
        } else defaultCloseOperationString = "";
        return super.paramString() + ",closable=" + closableString + ",defaultCloseOperation=" + defaultCloseOperationString + ",desktopIcon=" + desktopIconString + ",frameIcon=" + frameIconString + ",iconable=" + iconableString + ",isClosed=" + isClosedString + ",isIcon=" + isIconString + ",isMaximum=" + isMaximumString + ",isSelected=" + isSelectedString + ",maximizable=" + maximizableString + ",opened=" + openedString + ",resizable=" + resizableString + ",rootPane=" + rootPaneString + ",rootPaneCheckingEnabled=" + rootPaneCheckingEnabledString + ",title=" + titleString;
    }
    boolean isDragging = false;
    boolean danger = false;
    
    protected void paintComponent(Graphics g) {
        if (isDragging) {
            danger = true;
        }
        super.paintComponent(g);
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JInternalFrame$AccessibleJInternalFrame(this);
        }
        return accessibleContext;
    }
    {
    }
    {
    }
}
