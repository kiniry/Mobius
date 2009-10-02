package javax.swing.plaf.metal;

import java.awt.*;
import java.beans.*;
import javax.swing.*;

class MetalFontDesktopProperty extends com.sun.java.swing.plaf.windows.DesktopProperty {
    private static final String[] propertyMapping = {"win.ansiVar.font.height", "win.tooltip.font.height", "win.ansiVar.font.height", "win.menu.font.height", "win.frame.captionFont.height", "win.menu.font.height"};
    private int type;
    
    MetalFontDesktopProperty(int type) {
        this(propertyMapping[type], Toolkit.getDefaultToolkit(), type);
    }
    
    MetalFontDesktopProperty(String key, Toolkit kit, int type) {
        super(key, null, kit);
        this.type = type;
    }
    
    protected Object configureValue(Object value) {
        if (value instanceof Integer) {
            value = new Font(DefaultMetalTheme.getDefaultFontName(type), DefaultMetalTheme.getDefaultFontStyle(type), ((Integer)(Integer)value).intValue());
        }
        return super.configureValue(value);
    }
    
    protected Object getDefaultValue() {
        return new Font(DefaultMetalTheme.getDefaultFontName(type), DefaultMetalTheme.getDefaultFontStyle(type), DefaultMetalTheme.getDefaultFontSize(type));
    }
}
