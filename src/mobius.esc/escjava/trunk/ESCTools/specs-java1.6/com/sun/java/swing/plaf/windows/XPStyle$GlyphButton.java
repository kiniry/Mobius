package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.awt.image.*;
import java.io.*;
import java.util.*;
import java.util.prefs.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class XPStyle$GlyphButton extends JButton {
    private XPStyle$Skin skin;
    
    public XPStyle$GlyphButton(Component parent, TMSchema$Part part) {
        
        XPStyle xp = XPStyle.getXP();
        skin = xp.getSkin(parent, part);
        setBorder(null);
        setContentAreaFilled(false);
    }
    
    public boolean isFocusTraversable() {
        return false;
    }
    
    protected TMSchema$State getState() {
        TMSchema$State state = TMSchema$State.NORMAL;
        if (!isEnabled()) {
            state = TMSchema$State.DISABLED;
        } else if (getModel().isPressed()) {
            state = TMSchema$State.PRESSED;
        } else if (getModel().isRollover()) {
            state = TMSchema$State.HOT;
        }
        return state;
    }
    
    public void paintComponent(Graphics g) {
        Dimension d = getSize();
        skin.paintSkin(g, 0, 0, d.width, d.height, getState());
    }
    
    public void setPart(Component parent, TMSchema$Part part) {
        XPStyle xp = XPStyle.getXP();
        skin = xp.getSkin(parent, part);
        revalidate();
        repaint();
    }
    
    protected void paintBorder(Graphics g) {
    }
    
    public Dimension getPreferredSize() {
        return new Dimension(16, 16);
    }
    
    public Dimension getMinimumSize() {
        return new Dimension(5, 5);
    }
    
    public Dimension getMaximumSize() {
        return new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE);
    }
}
