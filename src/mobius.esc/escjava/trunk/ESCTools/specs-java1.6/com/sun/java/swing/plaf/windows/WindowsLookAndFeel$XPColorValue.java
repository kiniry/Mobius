package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$XPColorValue extends WindowsLookAndFeel$XPValue {
    
    WindowsLookAndFeel$XPColorValue(TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop, Object classicValue) {
        super(new WindowsLookAndFeel$XPColorValue$XPColorValueKey(part, state, prop), classicValue);
    }
    
    public Object getXPValue(UIDefaults table) {
        WindowsLookAndFeel$XPColorValue$XPColorValueKey key = (WindowsLookAndFeel$XPColorValue$XPColorValueKey)(WindowsLookAndFeel$XPColorValue$XPColorValueKey)xpValue;
        return XPStyle.getXP().getColor(key.skin, key.prop, null);
    }
    {
    }
}
