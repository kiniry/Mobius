package javax.swing;

import java.awt.Font;
import java.awt.Color;
import java.awt.Component;
import java.awt.Toolkit;
import javax.swing.text.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import com.sun.java.swing.SwingUtilities2;

public abstract class LookAndFeel {
    
    public LookAndFeel() {
        
    }
    
    public static void installColors(JComponent c, String defaultBgName, String defaultFgName) {
        Color bg = c.getBackground();
        if (bg == null || bg instanceof UIResource) {
            c.setBackground(UIManager.getColor(defaultBgName));
        }
        Color fg = c.getForeground();
        if (fg == null || fg instanceof UIResource) {
            c.setForeground(UIManager.getColor(defaultFgName));
        }
    }
    
    public static void installColorsAndFont(JComponent c, String defaultBgName, String defaultFgName, String defaultFontName) {
        Font f = c.getFont();
        if (f == null || f instanceof UIResource) {
            c.setFont(UIManager.getFont(defaultFontName));
        }
        installColors(c, defaultBgName, defaultFgName);
    }
    
    public static void installBorder(JComponent c, String defaultBorderName) {
        Border b = c.getBorder();
        if (b == null || b instanceof UIResource) {
            c.setBorder(UIManager.getBorder(defaultBorderName));
        }
    }
    
    public static void uninstallBorder(JComponent c) {
        if (c.getBorder() instanceof UIResource) {
            c.setBorder(null);
        }
    }
    
    public static void installProperty(JComponent c, String propertyName, Object propertyValue) {
        c.setUIProperty(propertyName, propertyValue);
    }
    
    public static JTextComponent$KeyBinding[] makeKeyBindings(Object[] keyBindingList) {
        JTextComponent$KeyBinding[] rv = new JTextComponent$KeyBinding[keyBindingList.length / 2];
        for (int i = 0; i < keyBindingList.length; i += 2) {
            KeyStroke keystroke = (keyBindingList[i] instanceof KeyStroke) ? (KeyStroke)(KeyStroke)keyBindingList[i] : KeyStroke.getKeyStroke((String)(String)keyBindingList[i]);
            String action = (String)(String)keyBindingList[i + 1];
            rv[i / 2] = new JTextComponent$KeyBinding(keystroke, action);
        }
        return rv;
    }
    
    public static InputMap makeInputMap(Object[] keys) {
        InputMap retMap = new InputMapUIResource();
        loadKeyBindings(retMap, keys);
        return retMap;
    }
    
    public static ComponentInputMap makeComponentInputMap(JComponent c, Object[] keys) {
        ComponentInputMap retMap = new ComponentInputMapUIResource(c);
        loadKeyBindings(retMap, keys);
        return retMap;
    }
    
    public static void loadKeyBindings(InputMap retMap, Object[] keys) {
        if (keys != null) {
            for (int counter = 0, maxCounter = keys.length; counter < maxCounter; counter++) {
                Object keyStrokeO = keys[counter++];
                KeyStroke ks = (keyStrokeO instanceof KeyStroke) ? (KeyStroke)(KeyStroke)keyStrokeO : KeyStroke.getKeyStroke((String)(String)keyStrokeO);
                retMap.put(ks, keys[counter]);
            }
        }
    }
    
    public static Object makeIcon(final Class baseClass, final String gifFile) {
        return SwingUtilities2.makeIcon(baseClass, baseClass, gifFile);
    }
    
    public void provideErrorFeedback(Component component) {
        Toolkit toolkit = null;
        if (component != null) {
            toolkit = component.getToolkit();
        } else {
            toolkit = Toolkit.getDefaultToolkit();
        }
        toolkit.beep();
    }
    
    public static Object getDesktopPropertyValue(String systemPropertyName, Object fallbackValue) {
        Object value = Toolkit.getDefaultToolkit().getDesktopProperty(systemPropertyName);
        if (value == null) {
            return fallbackValue;
        } else if (value instanceof Color) {
            return new ColorUIResource((Color)(Color)value);
        } else if (value instanceof Font) {
            return new FontUIResource((Font)(Font)value);
        }
        return value;
    }
    
    public Icon getDisabledIcon(JComponent component, Icon icon) {
        if (icon instanceof ImageIcon) {
            return new IconUIResource(new ImageIcon(GrayFilter.createDisabledImage(((ImageIcon)(ImageIcon)icon).getImage())));
        }
        return null;
    }
    
    public Icon getDisabledSelectedIcon(JComponent component, Icon icon) {
        return getDisabledIcon(component, icon);
    }
    
    public abstract String getName();
    
    public abstract String getID();
    
    public abstract String getDescription();
    
    public boolean getSupportsWindowDecorations() {
        return false;
    }
    
    public abstract boolean isNativeLookAndFeel();
    
    public abstract boolean isSupportedLookAndFeel();
    
    public void initialize() {
    }
    
    public void uninitialize() {
    }
    
    public UIDefaults getDefaults() {
        return null;
    }
    
    public String toString() {
        return "[" + getDescription() + " - " + getClass().getName() + "]";
    }
}
