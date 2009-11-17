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

class XPStyle$XPImageBorder extends AbstractBorder implements UIResource {
    /*synthetic*/ final XPStyle this$0;
    XPStyle$Skin skin;
    
    XPStyle$XPImageBorder(/*synthetic*/ final XPStyle this$0, Component c, TMSchema$Part part) {
        this.this$0 = this$0;
        
        this.skin = this$0.getSkin(c, part);
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        skin.paintSkin(g, x, y, width, height, null);
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        Insets margin = null;
        Insets borderInsets = skin.getContentMargin();
        if (c instanceof AbstractButton) {
            margin = ((AbstractButton)(AbstractButton)c).getMargin();
        } else if (c instanceof JToolBar) {
            margin = ((JToolBar)(JToolBar)c).getMargin();
        } else if (c instanceof JTextComponent) {
            margin = ((JTextComponent)(JTextComponent)c).getMargin();
        }
        insets.top = (margin != null ? margin.top : 0) + borderInsets.top;
        insets.left = (margin != null ? margin.left : 0) + borderInsets.left;
        insets.bottom = (margin != null ? margin.bottom : 0) + borderInsets.bottom;
        insets.right = (margin != null ? margin.right : 0) + borderInsets.right;
        return insets;
    }
}
