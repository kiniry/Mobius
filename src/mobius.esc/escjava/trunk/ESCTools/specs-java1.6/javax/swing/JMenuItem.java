package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.beans.PropertyChangeListener;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.event.*;
import javax.accessibility.*;

public class JMenuItem extends AbstractButton implements Accessible, MenuElement {
    {
    }
    private static final String uiClassID = "MenuItemUI";
    private static final boolean TRACE = false;
    private static final boolean VERBOSE = false;
    private static final boolean DEBUG = false;
    private boolean isMouseDragged = false;
    
    public JMenuItem() {
        this(null, (Icon)null);
    }
    
    public JMenuItem(Icon icon) {
        this(null, icon);
    }
    
    public JMenuItem(String text) {
        this(text, (Icon)null);
    }
    
    public JMenuItem(Action a) {
        this();
        setAction(a);
    }
    
    public JMenuItem(String text, Icon icon) {
        
        setModel(new DefaultButtonModel());
        init(text, icon);
        initFocusability();
    }
    
    public JMenuItem(String text, int mnemonic) {
        
        setModel(new DefaultButtonModel());
        init(text, null);
        setMnemonic(mnemonic);
        initFocusability();
    }
    
    void initFocusability() {
        setFocusable(false);
    }
    
    protected void init(String text, Icon icon) {
        if (text != null) {
            setText(text);
        }
        if (icon != null) {
            setIcon(icon);
        }
        addFocusListener(new JMenuItem$MenuItemFocusListener(null));
        setUIProperty("borderPainted", Boolean.FALSE);
        setFocusPainted(false);
        setHorizontalTextPosition(JButton.TRAILING);
        setHorizontalAlignment(JButton.LEADING);
        updateUI();
    }
    {
    }
    
    public void setUI(MenuItemUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((MenuItemUI)(MenuItemUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public void setArmed(boolean b) {
        ButtonModel model = (ButtonModel)getModel();
        boolean oldValue = model.isArmed();
        if (model.isArmed() != b) {
            model.setArmed(b);
        }
    }
    
    public boolean isArmed() {
        ButtonModel model = (ButtonModel)getModel();
        return model.isArmed();
    }
    
    public void setEnabled(boolean b) {
        if (b == false) setArmed(false);
        super.setEnabled(b);
    }
    
    boolean alwaysOnTop() {
        if (SwingUtilities.getAncestorOfClass(JInternalFrame.class, this) != null) {
            return false;
        }
        return true;
    }
    private KeyStroke accelerator;
    
    public void setAccelerator(KeyStroke keyStroke) {
        KeyStroke oldAccelerator = accelerator;
        this.accelerator = keyStroke;
        firePropertyChange("accelerator", oldAccelerator, accelerator);
    }
    
    public KeyStroke getAccelerator() {
        return this.accelerator;
    }
    
    protected void configurePropertiesFromAction(Action a) {
        super.configurePropertiesFromAction(a);
        KeyStroke ks = (a == null) ? null : (KeyStroke)(KeyStroke)a.getValue(Action.ACCELERATOR_KEY);
        setAccelerator(ks == null ? null : ks);
    }
    
    protected PropertyChangeListener createActionPropertyChangeListener(Action a) {
        return new JMenuItem$MenuItemPropertyChangeListener(this, a);
    }
    {
    }
    
    public void processMouseEvent(MouseEvent e, MenuElement[] path, MenuSelectionManager manager) {
        processMenuDragMouseEvent(new MenuDragMouseEvent(e.getComponent(), e.getID(), e.getWhen(), e.getModifiers(), e.getX(), e.getY(), e.getClickCount(), e.isPopupTrigger(), path, manager));
    }
    
    public void processKeyEvent(KeyEvent e, MenuElement[] path, MenuSelectionManager manager) {
        ;
        MenuKeyEvent mke = new MenuKeyEvent(e.getComponent(), e.getID(), e.getWhen(), e.getModifiers(), e.getKeyCode(), e.getKeyChar(), path, manager);
        processMenuKeyEvent(mke);
        if (mke.isConsumed()) {
            e.consume();
        }
    }
    
    public void processMenuDragMouseEvent(MenuDragMouseEvent e) {
        switch (e.getID()) {
        case MouseEvent.MOUSE_ENTERED: 
            isMouseDragged = false;
            fireMenuDragMouseEntered(e);
            break;
        
        case MouseEvent.MOUSE_EXITED: 
            isMouseDragged = false;
            fireMenuDragMouseExited(e);
            break;
        
        case MouseEvent.MOUSE_DRAGGED: 
            isMouseDragged = true;
            fireMenuDragMouseDragged(e);
            break;
        
        case MouseEvent.MOUSE_RELEASED: 
            if (isMouseDragged) fireMenuDragMouseReleased(e);
            break;
        
        default: 
            break;
        
        }
    }
    
    public void processMenuKeyEvent(MenuKeyEvent e) {
        ;
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
    
    protected void fireMenuDragMouseEntered(MenuDragMouseEvent event) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuDragMouseListener.class) {
                ((MenuDragMouseListener)(MenuDragMouseListener)listeners[i + 1]).menuDragMouseEntered(event);
            }
        }
    }
    
    protected void fireMenuDragMouseExited(MenuDragMouseEvent event) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuDragMouseListener.class) {
                ((MenuDragMouseListener)(MenuDragMouseListener)listeners[i + 1]).menuDragMouseExited(event);
            }
        }
    }
    
    protected void fireMenuDragMouseDragged(MenuDragMouseEvent event) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuDragMouseListener.class) {
                ((MenuDragMouseListener)(MenuDragMouseListener)listeners[i + 1]).menuDragMouseDragged(event);
            }
        }
    }
    
    protected void fireMenuDragMouseReleased(MenuDragMouseEvent event) {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuDragMouseListener.class) {
                ((MenuDragMouseListener)(MenuDragMouseListener)listeners[i + 1]).menuDragMouseReleased(event);
            }
        }
    }
    
    protected void fireMenuKeyPressed(MenuKeyEvent event) {
        ;
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuKeyListener.class) {
                ((MenuKeyListener)(MenuKeyListener)listeners[i + 1]).menuKeyPressed(event);
            }
        }
    }
    
    protected void fireMenuKeyReleased(MenuKeyEvent event) {
        ;
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuKeyListener.class) {
                ((MenuKeyListener)(MenuKeyListener)listeners[i + 1]).menuKeyReleased(event);
            }
        }
    }
    
    protected void fireMenuKeyTyped(MenuKeyEvent event) {
        ;
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == MenuKeyListener.class) {
                ((MenuKeyListener)(MenuKeyListener)listeners[i + 1]).menuKeyTyped(event);
            }
        }
    }
    
    public void menuSelectionChanged(boolean isIncluded) {
        setArmed(isIncluded);
    }
    
    public MenuElement[] getSubElements() {
        return new MenuElement[0];
    }
    
    public Component getComponent() {
        return this;
    }
    
    public void addMenuDragMouseListener(MenuDragMouseListener l) {
        listenerList.add(MenuDragMouseListener.class, l);
    }
    
    public void removeMenuDragMouseListener(MenuDragMouseListener l) {
        listenerList.remove(MenuDragMouseListener.class, l);
    }
    
    public MenuDragMouseListener[] getMenuDragMouseListeners() {
        return (MenuDragMouseListener[])(MenuDragMouseListener[])listenerList.getListeners(MenuDragMouseListener.class);
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
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        if (getUIClassID().equals(uiClassID)) {
            updateUI();
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    protected String paramString() {
        return super.paramString();
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JMenuItem$AccessibleJMenuItem(this);
        }
        return accessibleContext;
    }
    {
    }
}
