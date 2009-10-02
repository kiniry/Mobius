package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import javax.swing.plaf.basic.*;
import javax.swing.*;
import javax.swing.plaf.*;
import javax.swing.tree.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;
import com.sun.java.swing.plaf.windows.XPStyle.Skin;

public class WindowsTreeUI$CollapsedIcon extends WindowsTreeUI$ExpandedIcon {
    
    public WindowsTreeUI$CollapsedIcon() {
        
    }
    
    public static Icon createCollapsedIcon() {
        return new WindowsTreeUI$CollapsedIcon();
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        XPStyle$Skin skin = getSkin(c);
        if (skin != null) {
            skin.paintSkin(g, x, y, TMSchema$State.CLOSED);
        } else {
            super.paintIcon(c, g, x, y);
            g.drawLine(x + 4, y + 2, x + 4, y + (9 - 3));
        }
    }
}
