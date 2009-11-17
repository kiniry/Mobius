package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$WindowsFontSizeProperty extends DesktopProperty {
    private String fontName;
    private int fontSize;
    private int fontStyle;
    
    WindowsLookAndFeel$WindowsFontSizeProperty(String key, Toolkit toolkit, String fontName, int fontStyle, int fontSize) {
        super(key, null, toolkit);
        this.fontName = fontName;
        this.fontSize = fontSize;
        this.fontStyle = fontStyle;
    }
    
    protected Object configureValue(Object value) {
        if (value == null) {
            value = new FontUIResource(fontName, fontStyle, fontSize);
        } else if (value instanceof Integer) {
            value = new FontUIResource(fontName, fontStyle, ((Integer)(Integer)value).intValue());
        }
        return value;
    }
}
