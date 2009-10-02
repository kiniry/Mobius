package java.awt;

import java.awt.event.KeyEvent;

public class MenuShortcut implements java.io.Serializable {
    int key;
    boolean usesShift;
    private static final long serialVersionUID = 143448358473180225L;
    
    public MenuShortcut(int key) {
        this(key, false);
    }
    
    public MenuShortcut(int key, boolean useShiftModifier) {
        
        this.key = key;
        this.usesShift = useShiftModifier;
    }
    
    public int getKey() {
        return key;
    }
    
    public boolean usesShiftModifier() {
        return usesShift;
    }
    
    public boolean equals(MenuShortcut s) {
        return (s != null && (s.getKey() == key) && (s.usesShiftModifier() == usesShift));
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof MenuShortcut) {
            return equals((MenuShortcut)(MenuShortcut)obj);
        }
        return false;
    }
    
    public int hashCode() {
        return (usesShift) ? (~key) : key;
    }
    
    public String toString() {
        int modifiers = 0;
        if (!GraphicsEnvironment.isHeadless()) {
            modifiers = Toolkit.getDefaultToolkit().getMenuShortcutKeyMask();
        }
        if (usesShiftModifier()) {
            modifiers |= Event.SHIFT_MASK;
        }
        return KeyEvent.getKeyModifiersText(modifiers) + "+" + KeyEvent.getKeyText(key);
    }
    
    protected String paramString() {
        String str = "key=" + key;
        if (usesShiftModifier()) {
            str += ",usesShiftModifier";
        }
        return str;
    }
}
