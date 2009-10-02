package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$XPBorderValue extends WindowsLookAndFeel$XPValue {
    private final Border extraMargin;
    
    WindowsLookAndFeel$XPBorderValue(TMSchema$Part xpValue, Object classicValue) {
        this(xpValue, classicValue, null);
    }
    
    WindowsLookAndFeel$XPBorderValue(TMSchema$Part xpValue, Object classicValue, Border extraMargin) {
        super(xpValue, classicValue);
        this.extraMargin = extraMargin;
    }
    
    public Object getXPValue(UIDefaults table) {
        Border xpBorder = XPStyle.getXP().getBorder(null, (TMSchema$Part)(TMSchema$Part)xpValue);
        if (extraMargin != null) {
            return new BorderUIResource$CompoundBorderUIResource(xpBorder, extraMargin);
        } else {
            return xpBorder;
        }
    }
}
