package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.awt.image.*;
import java.io.*;
import java.util.*;
import java.util.prefs.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import sun.awt.windows.ThemeReader;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class XPStyle$Skin {
    
    /*synthetic*/ static String access$000(XPStyle$Skin x0) {
        return x0.string;
    }
    final Component component;
    final TMSchema$Part part;
    final TMSchema$State state;
    private final String string;
    private Dimension size = null;
    
    XPStyle$Skin(Component component, TMSchema$Part part) {
        this(component, part, null);
    }
    
    XPStyle$Skin(TMSchema$Part part, TMSchema$State state) {
        this(null, part, state);
    }
    
    XPStyle$Skin(Component component, TMSchema$Part part, TMSchema$State state) {
        
        this.component = component;
        this.part = part;
        this.state = state;
        String str = part.getControlName(component) + "." + part.name();
        if (state != null) {
            str += "(" + state.name() + ")";
        }
        string = str;
    }
    
    Insets getContentMargin() {
        return ThemeReader.getThemeMargins(part.getControlName(null), part.getValue(), 0, TMSchema$Prop.SIZINGMARGINS.getValue());
    }
    
    private int getWidth(TMSchema$State state) {
        if (size == null) {
            size = XPStyle.access$100(part, state);
        }
        return size.width;
    }
    
    int getWidth() {
        return getWidth((state != null) ? state : TMSchema$State.NORMAL);
    }
    
    private int getHeight(TMSchema$State state) {
        if (size == null) {
            size = XPStyle.access$100(part, state);
        }
        return size.height;
    }
    
    int getHeight() {
        return getHeight((state != null) ? state : TMSchema$State.NORMAL);
    }
    
    public String toString() {
        return string;
    }
    
    public boolean equals(Object obj) {
        return (obj instanceof XPStyle$Skin && ((XPStyle$Skin)(XPStyle$Skin)obj).string.equals(string));
    }
    
    public int hashCode() {
        return string.hashCode();
    }
    
    void paintSkin(Graphics g, int dx, int dy, TMSchema$State state) {
        if (state == null) {
            state = this.state;
        }
        paintSkin(g, dx, dy, getWidth(state), getHeight(state), state);
    }
    
    void paintSkin(Graphics g, Rectangle r, TMSchema$State state) {
        paintSkin(g, r.x, r.y, r.width, r.height, state);
    }
    
    void paintSkin(Graphics g, int dx, int dy, int dw, int dh, TMSchema$State state) {
        XPStyle.access$200().paint(null, g, dx, dy, dw, dh, new Object[]{this, state});
    }
    
    void paintSkin(Graphics g, int dx, int dy, int dw, int dh, TMSchema$State state, boolean borderFill) {
        if (borderFill && "borderfill".equals(XPStyle.access$300(component, part, state, TMSchema$Prop.BGTYPE))) {
            return;
        }
        XPStyle.access$200().paint(null, g, dx, dy, dw, dh, new Object[]{this, state});
    }
}
