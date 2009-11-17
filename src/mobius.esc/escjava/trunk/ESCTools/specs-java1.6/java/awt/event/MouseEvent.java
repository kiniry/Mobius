package java.awt.event;

import java.awt.Component;
import java.awt.GraphicsEnvironment;
import java.awt.Point;
import java.awt.Toolkit;
import java.io.IOException;
import java.io.ObjectInputStream;

public class MouseEvent extends InputEvent {
    public static final int MOUSE_FIRST = 500;
    public static final int MOUSE_LAST = 507;
    public static final int MOUSE_CLICKED = MOUSE_FIRST;
    public static final int MOUSE_PRESSED = 1 + MOUSE_FIRST;
    public static final int MOUSE_RELEASED = 2 + MOUSE_FIRST;
    public static final int MOUSE_MOVED = 3 + MOUSE_FIRST;
    public static final int MOUSE_ENTERED = 4 + MOUSE_FIRST;
    public static final int MOUSE_EXITED = 5 + MOUSE_FIRST;
    public static final int MOUSE_DRAGGED = 6 + MOUSE_FIRST;
    public static final int MOUSE_WHEEL = 7 + MOUSE_FIRST;
    public static final int NOBUTTON = 0;
    public static final int BUTTON1 = 1;
    public static final int BUTTON2 = 2;
    public static final int BUTTON3 = 3;
    int x;
    int y;
    int clickCount;
    int button;
    boolean popupTrigger = false;
    private static final long serialVersionUID = -991214153494842848L;
    static {
        NativeLibLoader.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    private static native void initIDs();
    
    public MouseEvent(Component source, int id, long when, int modifiers, int x, int y, int clickCount, boolean popupTrigger, int button) {
        super(source, id, when, modifiers);
        this.x = x;
        this.y = y;
        this.clickCount = clickCount;
        this.popupTrigger = popupTrigger;
        if (button < NOBUTTON || button > BUTTON3) {
            throw new IllegalArgumentException("Invalid button value");
        }
        this.button = button;
        if ((getModifiers() != 0) && (getModifiersEx() == 0)) {
            setNewModifiers();
        } else if ((getModifiers() == 0) && (getModifiersEx() != 0 || button != NOBUTTON)) {
            setOldModifiers();
        }
    }
    
    public MouseEvent(Component source, int id, long when, int modifiers, int x, int y, int clickCount, boolean popupTrigger) {
        this(source, id, when, modifiers, x, y, clickCount, popupTrigger, NOBUTTON);
    }
    
    public int getX() {
        return x;
    }
    
    public int getY() {
        return y;
    }
    
    public Point getPoint() {
        int x;
        int y;
        synchronized (this) {
            x = this.x;
            y = this.y;
        }
        return new Point(x, y);
    }
    
    public synchronized void translatePoint(int x, int y) {
        this.x += x;
        this.y += y;
    }
    
    public int getClickCount() {
        return clickCount;
    }
    
    public int getButton() {
        return button;
    }
    
    public boolean isPopupTrigger() {
        return popupTrigger;
    }
    
    public static String getMouseModifiersText(int modifiers) {
        StringBuffer buf = new StringBuffer();
        if ((modifiers & InputEvent.ALT_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.alt", "Alt"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.META_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.meta", "Meta"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.CTRL_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.control", "Ctrl"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.SHIFT_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.shift", "Shift"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.ALT_GRAPH_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.altGraph", "Alt Graph"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.BUTTON1_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.button1", "Button1"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.BUTTON2_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.button2", "Button2"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.BUTTON3_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.button3", "Button3"));
            buf.append("+");
        }
        if (buf.length() > 0) {
            buf.setLength(buf.length() - 1);
        }
        return buf.toString();
    }
    
    public String paramString() {
        StringBuffer str = new StringBuffer(80);
        switch (id) {
        case MOUSE_PRESSED: 
            str.append("MOUSE_PRESSED");
            break;
        
        case MOUSE_RELEASED: 
            str.append("MOUSE_RELEASED");
            break;
        
        case MOUSE_CLICKED: 
            str.append("MOUSE_CLICKED");
            break;
        
        case MOUSE_ENTERED: 
            str.append("MOUSE_ENTERED");
            break;
        
        case MOUSE_EXITED: 
            str.append("MOUSE_EXITED");
            break;
        
        case MOUSE_MOVED: 
            str.append("MOUSE_MOVED");
            break;
        
        case MOUSE_DRAGGED: 
            str.append("MOUSE_DRAGGED");
            break;
        
        case MOUSE_WHEEL: 
            str.append("MOUSE_WHEEL");
            break;
        
        default: 
            str.append("unknown type");
        
        }
        str.append(",(").append(x).append(",").append(y).append(")");
        str.append(",button=").append(getButton());
        if (getModifiers() != 0) {
            str.append(",modifiers=").append(getMouseModifiersText(modifiers));
        }
        if (getModifiersEx() != 0) {
            str.append(",extModifiers=").append(getModifiersExText(modifiers));
        }
        str.append(",clickCount=").append(clickCount);
        return str.toString();
    }
    
    private void setNewModifiers() {
        if ((modifiers & BUTTON1_MASK) != 0) {
            modifiers |= BUTTON1_DOWN_MASK;
        }
        if ((modifiers & BUTTON2_MASK) != 0) {
            modifiers |= BUTTON2_DOWN_MASK;
        }
        if ((modifiers & BUTTON3_MASK) != 0) {
            modifiers |= BUTTON3_DOWN_MASK;
        }
        if (id == MOUSE_PRESSED || id == MOUSE_RELEASED || id == MOUSE_CLICKED) {
            if ((modifiers & BUTTON1_MASK) != 0) {
                button = BUTTON1;
                modifiers &= ~BUTTON2_MASK & ~BUTTON3_MASK;
                if (id != MOUSE_PRESSED) {
                    modifiers &= ~BUTTON1_DOWN_MASK;
                }
            } else if ((modifiers & BUTTON2_MASK) != 0) {
                button = BUTTON2;
                modifiers &= ~BUTTON1_MASK & ~BUTTON3_MASK;
                if (id != MOUSE_PRESSED) {
                    modifiers &= ~BUTTON2_DOWN_MASK;
                }
            } else if ((modifiers & BUTTON3_MASK) != 0) {
                button = BUTTON3;
                modifiers &= ~BUTTON1_MASK & ~BUTTON2_MASK;
                if (id != MOUSE_PRESSED) {
                    modifiers &= ~BUTTON3_DOWN_MASK;
                }
            }
        }
        if ((modifiers & InputEvent.ALT_MASK) != 0) {
            modifiers |= InputEvent.ALT_DOWN_MASK;
        }
        if ((modifiers & InputEvent.META_MASK) != 0) {
            modifiers |= InputEvent.META_DOWN_MASK;
        }
        if ((modifiers & InputEvent.SHIFT_MASK) != 0) {
            modifiers |= InputEvent.SHIFT_DOWN_MASK;
        }
        if ((modifiers & InputEvent.CTRL_MASK) != 0) {
            modifiers |= InputEvent.CTRL_DOWN_MASK;
        }
        if ((modifiers & InputEvent.ALT_GRAPH_MASK) != 0) {
            modifiers |= InputEvent.ALT_GRAPH_DOWN_MASK;
        }
    }
    
    private void setOldModifiers() {
        if (id == MOUSE_PRESSED || id == MOUSE_RELEASED || id == MOUSE_CLICKED) {
            switch (button) {
            case BUTTON1: 
                modifiers |= BUTTON1_MASK;
                break;
            
            case BUTTON2: 
                modifiers |= BUTTON2_MASK;
                break;
            
            case BUTTON3: 
                modifiers |= BUTTON3_MASK;
                break;
            
            }
        } else {
            if ((modifiers & BUTTON1_DOWN_MASK) != 0) {
                modifiers |= BUTTON1_MASK;
            }
            if ((modifiers & BUTTON2_DOWN_MASK) != 0) {
                modifiers |= BUTTON2_MASK;
            }
            if ((modifiers & BUTTON3_DOWN_MASK) != 0) {
                modifiers |= BUTTON3_MASK;
            }
        }
        if ((modifiers & ALT_DOWN_MASK) != 0) {
            modifiers |= ALT_MASK;
        }
        if ((modifiers & META_DOWN_MASK) != 0) {
            modifiers |= META_MASK;
        }
        if ((modifiers & SHIFT_DOWN_MASK) != 0) {
            modifiers |= SHIFT_MASK;
        }
        if ((modifiers & CTRL_DOWN_MASK) != 0) {
            modifiers |= CTRL_MASK;
        }
        if ((modifiers & ALT_GRAPH_DOWN_MASK) != 0) {
            modifiers |= ALT_GRAPH_MASK;
        }
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        if (getModifiers() != 0 && getModifiersEx() == 0) {
            setNewModifiers();
        }
    }
}
