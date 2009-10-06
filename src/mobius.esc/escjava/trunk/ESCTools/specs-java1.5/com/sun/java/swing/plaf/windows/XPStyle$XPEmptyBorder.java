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

class XPStyle$XPEmptyBorder extends EmptyBorder implements UIResource {
    /*synthetic*/ final XPStyle this$0;
    
    XPStyle$XPEmptyBorder(/*synthetic*/ final XPStyle this$0, Insets m) {
        super(m.top + 2, m.left + 2, m.bottom + 2, m.right + 2);
        this.this$0 = this$0;
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, getBorderInsets());
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        insets = super.getBorderInsets(c, insets);
        Insets margin = null;
        if (c instanceof AbstractButton) {
            Insets m = ((AbstractButton)(AbstractButton)c).getMargin();
            if (c.getParent() instanceof JToolBar && !(c instanceof JRadioButton) && !(c instanceof JCheckBox) && m instanceof InsetsUIResource) {
                insets.top -= 2;
                insets.left -= 2;
                insets.bottom -= 2;
                insets.right -= 2;
            } else {
                margin = m;
            }
        } else if (c instanceof JToolBar) {
            margin = ((JToolBar)(JToolBar)c).getMargin();
        } else if (c instanceof JTextComponent) {
            margin = ((JTextComponent)(JTextComponent)c).getMargin();
        }
        if (margin != null) {
            insets.top = margin.top + 2;
            insets.left = margin.left + 2;
            insets.bottom = margin.bottom + 2;
            insets.right = margin.right + 2;
        }
        return insets;
    }
}
