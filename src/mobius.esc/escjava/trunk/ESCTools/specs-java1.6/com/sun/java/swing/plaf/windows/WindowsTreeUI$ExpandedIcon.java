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

public class WindowsTreeUI$ExpandedIcon implements Icon, Serializable {
    
    public WindowsTreeUI$ExpandedIcon() {
        
    }
    
    public static Icon createExpandedIcon() {
        return new WindowsTreeUI$ExpandedIcon();
    }
    
    XPStyle$Skin getSkin(Component c) {
        XPStyle xp = XPStyle.getXP();
        return (xp != null) ? xp.getSkin(c, TMSchema$Part.TVP_GLYPH) : null;
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        XPStyle$Skin skin = getSkin(c);
        if (skin != null) {
            skin.paintSkin(g, x, y, TMSchema$State.OPENED);
            return;
        }
        Color backgroundColor = c.getBackground();
        if (backgroundColor != null) g.setColor(backgroundColor); else g.setColor(Color.white);
        g.fillRect(x, y, 9 - 1, 9 - 1);
        g.setColor(Color.gray);
        g.drawRect(x, y, 9 - 1, 9 - 1);
        g.setColor(Color.black);
        g.drawLine(x + 2, y + 4, x + (9 - 3), y + 4);
    }
    
    public int getIconWidth() {
        XPStyle$Skin skin = getSkin(null);
        return (skin != null) ? skin.getWidth() : 9;
    }
    
    public int getIconHeight() {
        XPStyle$Skin skin = getSkin(null);
        return (skin != null) ? skin.getHeight() : 9;
    }
}
