package java.awt;

import java.util.EventObject;
import java.awt.event.*;
import java.awt.peer.ComponentPeer;
import java.awt.peer.LightweightPeer;
import java.lang.reflect.Field;

public abstract class AWTEvent extends EventObject {
    private byte[] bdata;
    protected int id;
    protected boolean consumed = false;
    transient boolean focusManagerIsDispatching = false;
    transient boolean isPosted;
    public static final long COMPONENT_EVENT_MASK = 1;
    public static final long CONTAINER_EVENT_MASK = 2;
    public static final long FOCUS_EVENT_MASK = 4;
    public static final long KEY_EVENT_MASK = 8;
    public static final long MOUSE_EVENT_MASK = 16;
    public static final long MOUSE_MOTION_EVENT_MASK = 32;
    public static final long WINDOW_EVENT_MASK = 64;
    public static final long ACTION_EVENT_MASK = 128;
    public static final long ADJUSTMENT_EVENT_MASK = 256;
    public static final long ITEM_EVENT_MASK = 512;
    public static final long TEXT_EVENT_MASK = 1024;
    public static final long INPUT_METHOD_EVENT_MASK = 2048;
    static final long INPUT_METHODS_ENABLED_MASK = 4096;
    public static final long PAINT_EVENT_MASK = 8192;
    public static final long INVOCATION_EVENT_MASK = 16384;
    public static final long HIERARCHY_EVENT_MASK = 32768;
    public static final long HIERARCHY_BOUNDS_EVENT_MASK = 65536;
    public static final long MOUSE_WHEEL_EVENT_MASK = 131072;
    public static final long WINDOW_STATE_EVENT_MASK = 262144;
    public static final long WINDOW_FOCUS_EVENT_MASK = 524288;
    public static final int RESERVED_ID_MAX = 1999;
    private static Field inputEvent_CanAccessSystemClipboard_Field = null;
    private static final long serialVersionUID = -1825314779160409405L;
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    private static synchronized Field get_InputEvent_CanAccessSystemClipboard() {
        if (inputEvent_CanAccessSystemClipboard_Field == null) {
            inputEvent_CanAccessSystemClipboard_Field = (Field)(Field)java.security.AccessController.doPrivileged(new AWTEvent$1());
        }
        return inputEvent_CanAccessSystemClipboard_Field;
    }
    
    private static native void initIDs();
    
    public AWTEvent(Event event) {
        this(event.target, event.id);
    }
    
    public AWTEvent(Object source, int id) {
        super(source);
        this.id = id;
        switch (id) {
        case ActionEvent.ACTION_PERFORMED: 
        
        case ItemEvent.ITEM_STATE_CHANGED: 
        
        case AdjustmentEvent.ADJUSTMENT_VALUE_CHANGED: 
        
        case TextEvent.TEXT_VALUE_CHANGED: 
            consumed = true;
            break;
        
        default: 
        
        }
    }
    
    public void setSource(Object newSource) {
        if (source == newSource) {
            return;
        }
        Component comp = null;
        if (newSource instanceof Component) {
            comp = (Component)(Component)newSource;
            while (comp != null && comp.peer != null && (comp.peer instanceof LightweightPeer)) {
                comp = comp.parent;
            }
        }
        synchronized (this) {
            source = newSource;
            if (comp != null) {
                ComponentPeer peer = comp.peer;
                if (peer != null) {
                    nativeSetSource(peer);
                }
            }
        }
    }
    
    private native void nativeSetSource(ComponentPeer peer);
    
    public int getID() {
        return id;
    }
    
    public String toString() {
        String srcName = null;
        if (source instanceof Component) {
            srcName = ((Component)(Component)source).getName();
        } else if (source instanceof MenuComponent) {
            srcName = ((MenuComponent)(MenuComponent)source).getName();
        }
        return getClass().getName() + "[" + paramString() + "] on " + (srcName != null ? srcName : source);
    }
    
    public String paramString() {
        return "";
    }
    
    protected void consume() {
        switch (id) {
        case KeyEvent.KEY_PRESSED: 
        
        case KeyEvent.KEY_RELEASED: 
        
        case MouseEvent.MOUSE_PRESSED: 
        
        case MouseEvent.MOUSE_RELEASED: 
        
        case MouseEvent.MOUSE_MOVED: 
        
        case MouseEvent.MOUSE_DRAGGED: 
        
        case MouseEvent.MOUSE_ENTERED: 
        
        case MouseEvent.MOUSE_EXITED: 
        
        case MouseEvent.MOUSE_WHEEL: 
        
        case InputMethodEvent.INPUT_METHOD_TEXT_CHANGED: 
        
        case InputMethodEvent.CARET_POSITION_CHANGED: 
            consumed = true;
            break;
        
        default: 
        
        }
    }
    
    protected boolean isConsumed() {
        return consumed;
    }
    
    Event convertToOld() {
        Object src = getSource();
        int newid = id;
        switch (id) {
        case KeyEvent.KEY_PRESSED: 
        
        case KeyEvent.KEY_RELEASED: 
            KeyEvent ke = (KeyEvent)(KeyEvent)this;
            if (ke.isActionKey()) {
                newid = (id == KeyEvent.KEY_PRESSED ? Event.KEY_ACTION : Event.KEY_ACTION_RELEASE);
            }
            int keyCode = ke.getKeyCode();
            if (keyCode == KeyEvent.VK_SHIFT || keyCode == KeyEvent.VK_CONTROL || keyCode == KeyEvent.VK_ALT) {
                return null;
            }
            return new Event(src, ke.getWhen(), newid, 0, 0, Event.getOldEventKey(ke), (ke.getModifiers() & ~InputEvent.BUTTON1_MASK));
        
        case MouseEvent.MOUSE_PRESSED: 
        
        case MouseEvent.MOUSE_RELEASED: 
        
        case MouseEvent.MOUSE_MOVED: 
        
        case MouseEvent.MOUSE_DRAGGED: 
        
        case MouseEvent.MOUSE_ENTERED: 
        
        case MouseEvent.MOUSE_EXITED: 
            MouseEvent me = (MouseEvent)(MouseEvent)this;
            Event olde = new Event(src, me.getWhen(), newid, me.getX(), me.getY(), 0, (me.getModifiers() & ~InputEvent.BUTTON1_MASK));
            olde.clickCount = me.getClickCount();
            return olde;
        
        case FocusEvent.FOCUS_GAINED: 
            return new Event(src, Event.GOT_FOCUS, null);
        
        case FocusEvent.FOCUS_LOST: 
            return new Event(src, Event.LOST_FOCUS, null);
        
        case WindowEvent.WINDOW_CLOSING: 
        
        case WindowEvent.WINDOW_ICONIFIED: 
        
        case WindowEvent.WINDOW_DEICONIFIED: 
            return new Event(src, newid, null);
        
        case ComponentEvent.COMPONENT_MOVED: 
            if (src instanceof Frame || src instanceof Dialog) {
                Point p = ((Component)(Component)src).getLocation();
                return new Event(src, 0, Event.WINDOW_MOVED, p.x, p.y, 0, 0);
            }
            break;
        
        case ActionEvent.ACTION_PERFORMED: 
            ActionEvent ae = (ActionEvent)(ActionEvent)this;
            String cmd;
            if (src instanceof Button) {
                cmd = ((Button)(Button)src).getLabel();
            } else if (src instanceof MenuItem) {
                cmd = ((MenuItem)(MenuItem)src).getLabel();
            } else {
                cmd = ae.getActionCommand();
            }
            return new Event(src, 0, newid, 0, 0, 0, ae.getModifiers(), cmd);
        
        case ItemEvent.ITEM_STATE_CHANGED: 
            ItemEvent ie = (ItemEvent)(ItemEvent)this;
            Object arg;
            if (src instanceof List) {
                newid = (ie.getStateChange() == ItemEvent.SELECTED ? Event.LIST_SELECT : Event.LIST_DESELECT);
                arg = ie.getItem();
            } else {
                newid = Event.ACTION_EVENT;
                if (src instanceof Choice) {
                    arg = ie.getItem();
                } else {
                    arg = new Boolean(ie.getStateChange() == ItemEvent.SELECTED);
                }
            }
            return new Event(src, newid, arg);
        
        case AdjustmentEvent.ADJUSTMENT_VALUE_CHANGED: 
            AdjustmentEvent aje = (AdjustmentEvent)(AdjustmentEvent)this;
            switch (aje.getAdjustmentType()) {
            case AdjustmentEvent.UNIT_INCREMENT: 
                newid = Event.SCROLL_LINE_DOWN;
                break;
            
            case AdjustmentEvent.UNIT_DECREMENT: 
                newid = Event.SCROLL_LINE_UP;
                break;
            
            case AdjustmentEvent.BLOCK_INCREMENT: 
                newid = Event.SCROLL_PAGE_DOWN;
                break;
            
            case AdjustmentEvent.BLOCK_DECREMENT: 
                newid = Event.SCROLL_PAGE_UP;
                break;
            
            case AdjustmentEvent.TRACK: 
                if (aje.getValueIsAdjusting()) {
                    newid = Event.SCROLL_ABSOLUTE;
                } else {
                    newid = Event.SCROLL_END;
                }
                break;
            
            default: 
                return null;
            
            }
            return new Event(src, newid, new Integer(aje.getValue()));
        
        default: 
        
        }
        return null;
    }
    
    void copyPrivateDataInto(AWTEvent that) {
        that.bdata = this.bdata;
        if (this instanceof InputEvent && that instanceof InputEvent) {
            Field field = get_InputEvent_CanAccessSystemClipboard();
            if (field != null) {
                try {
                    boolean b = field.getBoolean(this);
                    field.setBoolean(that, b);
                } catch (IllegalAccessException e) {
                }
            }
        }
    }
    
    void dispatched() {
        if (this instanceof InputEvent) {
            Field field = get_InputEvent_CanAccessSystemClipboard();
            if (field != null) {
                try {
                    field.setBoolean(this, false);
                } catch (IllegalAccessException e) {
                }
            }
        }
    }
}
