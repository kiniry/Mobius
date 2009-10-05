package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.awt.image.*;
import java.io.*;
import java.util.*;
import java.util.prefs.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.swing.text.JTextComponent;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class XPStyle$XPFillBorder extends LineBorder implements UIResource {
    /*synthetic*/ final XPStyle this$0;
    
    XPStyle$XPFillBorder(/*synthetic*/ final XPStyle this$0, Color color, int thickness) {
        super(color, thickness);
        this.this$0 = this$0;
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        Insets margin = null;
        if (c instanceof AbstractButton) {
            margin = ((AbstractButton)(AbstractButton)c).getMargin();
        } else if (c instanceof JToolBar) {
            margin = ((JToolBar)(JToolBar)c).getMargin();
        } else if (c instanceof JTextComponent) {
            margin = ((JTextComponent)(JTextComponent)c).getMargin();
        }
        insets.top = (margin != null ? margin.top : 0) + thickness;
        insets.left = (margin != null ? margin.left : 0) + thickness;
        insets.bottom = (margin != null ? margin.bottom : 0) + thickness;
        insets.right = (margin != null ? margin.right : 0) + thickness;
        return insets;
    }
}
