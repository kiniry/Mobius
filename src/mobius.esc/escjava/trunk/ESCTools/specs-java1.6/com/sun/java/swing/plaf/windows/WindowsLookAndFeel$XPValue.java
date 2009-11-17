package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$XPValue implements UIDefaults$ActiveValue {
    protected Object classicValue;
    protected Object xpValue;
    
    WindowsLookAndFeel$XPValue(Object xpValue, Object classicValue) {
        
        this.xpValue = xpValue;
        this.classicValue = classicValue;
    }
    
    public Object createValue(UIDefaults table) {
        Object value = null;
        if (XPStyle.getXP() != null) {
            value = getXPValue(table);
        }
        return (value != null) ? value : getClassicValue(table);
    }
    
    protected Object getXPValue(UIDefaults table) {
        return recursiveCreateValue(xpValue, table);
    }
    
    protected Object getClassicValue(UIDefaults table) {
        return recursiveCreateValue(classicValue, table);
    }
    
    private Object recursiveCreateValue(Object value, UIDefaults table) {
        if (value instanceof UIDefaults$LazyValue) {
            value = ((UIDefaults$LazyValue)(UIDefaults$LazyValue)value).createValue(table);
        }
        if (value instanceof UIDefaults$ActiveValue) {
            return ((UIDefaults$ActiveValue)(UIDefaults$ActiveValue)value).createValue(table);
        } else {
            return value;
        }
    }
}
