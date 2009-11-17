package java.awt.event;

import java.awt.Event;
import java.awt.Component;
import java.awt.GraphicsEnvironment;
import java.awt.Toolkit;

public abstract class InputEvent extends ComponentEvent {
    public static final int SHIFT_MASK = Event.SHIFT_MASK;
    public static final int CTRL_MASK = Event.CTRL_MASK;
    public static final int META_MASK = Event.META_MASK;
    public static final int ALT_MASK = Event.ALT_MASK;
    public static final int ALT_GRAPH_MASK = 1 << 5;
    public static final int BUTTON1_MASK = 1 << 4;
    public static final int BUTTON2_MASK = Event.ALT_MASK;
    public static final int BUTTON3_MASK = Event.META_MASK;
    public static final int SHIFT_DOWN_MASK = 1 << 6;
    public static final int CTRL_DOWN_MASK = 1 << 7;
    public static final int META_DOWN_MASK = 1 << 8;
    public static final int ALT_DOWN_MASK = 1 << 9;
    public static final int BUTTON1_DOWN_MASK = 1 << 10;
    public static final int BUTTON2_DOWN_MASK = 1 << 11;
    public static final int BUTTON3_DOWN_MASK = 1 << 12;
    public static final int ALT_GRAPH_DOWN_MASK = 1 << 13;
    static final int JDK_1_3_MODIFIERS = SHIFT_DOWN_MASK - 1;
    long when;
    int modifiers;
    private transient boolean canAccessSystemClipboard;
    static {
        NativeLibLoader.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    private static native void initIDs();
    
    InputEvent(Component source, int id, long when, int modifiers) {
        super(source, id);
        this.when = when;
        this.modifiers = modifiers;
        canAccessSystemClipboard = canAccessSystemClipboard();
    }
    
    private boolean canAccessSystemClipboard() {
        boolean b = false;
        if (!GraphicsEnvironment.isHeadless()) {
            SecurityManager sm = System.getSecurityManager();
            if (sm != null) {
                try {
                    sm.checkSystemClipboardAccess();
                    b = true;
                } catch (SecurityException se) {
                }
            } else {
                b = true;
            }
        }
        return b;
    }
    
    public boolean isShiftDown() {
        return (modifiers & SHIFT_MASK) != 0;
    }
    
    public boolean isControlDown() {
        return (modifiers & CTRL_MASK) != 0;
    }
    
    public boolean isMetaDown() {
        return (modifiers & META_MASK) != 0;
    }
    
    public boolean isAltDown() {
        return (modifiers & ALT_MASK) != 0;
    }
    
    public boolean isAltGraphDown() {
        return (modifiers & ALT_GRAPH_MASK) != 0;
    }
    
    public long getWhen() {
        return when;
    }
    
    public int getModifiers() {
        return modifiers & JDK_1_3_MODIFIERS;
    }
    
    public int getModifiersEx() {
        return modifiers & ~JDK_1_3_MODIFIERS;
    }
    
    public void consume() {
        consumed = true;
    }
    
    public boolean isConsumed() {
        return consumed;
    }
    static final long serialVersionUID = -2482525981698309786L;
    
    public static String getModifiersExText(int modifiers) {
        StringBuffer buf = new StringBuffer();
        if ((modifiers & InputEvent.META_DOWN_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.meta", "Meta"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.CTRL_DOWN_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.control", "Ctrl"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.ALT_DOWN_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.alt", "Alt"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.SHIFT_DOWN_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.shift", "Shift"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.ALT_GRAPH_DOWN_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.altGraph", "Alt Graph"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.BUTTON1_DOWN_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.button1", "Button1"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.BUTTON2_DOWN_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.button2", "Button2"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.BUTTON3_DOWN_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.button3", "Button3"));
            buf.append("+");
        }
        if (buf.length() > 0) {
            buf.setLength(buf.length() - 1);
        }
        return buf.toString();
    }
}
