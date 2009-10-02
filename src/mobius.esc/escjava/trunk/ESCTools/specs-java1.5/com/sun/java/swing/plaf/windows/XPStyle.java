package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.awt.image.*;
import java.io.*;
import java.security.AccessController;
import java.util.*;
import java.util.prefs.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import sun.awt.windows.ThemeReader;
import sun.security.action.GetPropertyAction;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class XPStyle {
    
    /*synthetic*/ static String access$300(Component x0, TMSchema$Part x1, TMSchema$State x2, TMSchema$Prop x3) {
        return getTypeEnumName(x0, x1, x2, x3);
    }
    
    /*synthetic*/ static XPStyle$SkinPainter access$200() {
        return skinPainter;
    }
    
    /*synthetic*/ static Dimension access$100(TMSchema$Part x0, TMSchema$State x1) {
        return getPartSize(x0, x1);
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !XPStyle.class.desiredAssertionStatus();
    private static XPStyle xp;
    private static XPStyle$SkinPainter skinPainter = new XPStyle$SkinPainter();
    private static Boolean themeActive = null;
    private HashMap borderMap;
    private HashMap colorMap;
    private boolean flatMenus;
    static {
        invalidateStyle();
    }
    
    static synchronized void invalidateStyle() {
        xp = null;
        themeActive = null;
    }
    
    static synchronized XPStyle getXP() {
        if (themeActive == null) {
            Toolkit toolkit = Toolkit.getDefaultToolkit();
            themeActive = (Boolean)(Boolean)toolkit.getDesktopProperty("win.xpstyle.themeActive");
            if (themeActive == null) {
                themeActive = Boolean.FALSE;
            }
            if (themeActive.booleanValue()) {
                GetPropertyAction propertyAction = new GetPropertyAction("swing.noxp");
                if (AccessController.doPrivileged(propertyAction) == null && ThemeReader.isThemed() && !(UIManager.getLookAndFeel() instanceof WindowsClassicLookAndFeel)) {
                    xp = new XPStyle();
                }
            }
        }
        return xp;
    }
    
    String getString(Component c, TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop) {
        return getTypeEnumName(c, part, state, prop);
    }
    
    private static String getTypeEnumName(Component c, TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop) {
        int enumValue = ThemeReader.getEnum(part.getControlName(c), part.getValue(), TMSchema$State.getValue(part, state), prop.getValue());
        if (enumValue == -1) {
            return null;
        }
        return TMSchema$TypeEnum.getTypeEnum(prop, enumValue).getName();
    }
    
    int getInt(Component c, TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop, int fallback) {
        return ThemeReader.getInt(part.getControlName(c), part.getValue(), TMSchema$State.getValue(part, state), prop.getValue());
    }
    
    Dimension getDimension(Component c, TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop) {
        return ThemeReader.getPosition(part.getControlName(c), part.getValue(), TMSchema$State.getValue(part, state), prop.getValue());
    }
    
    Point getPoint(Component c, TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop) {
        Dimension d = ThemeReader.getPosition(part.getControlName(c), part.getValue(), TMSchema$State.getValue(part, state), prop.getValue());
        if (d != null) {
            return new Point(d.width, d.height);
        } else {
            return null;
        }
    }
    
    Insets getMargin(Component c, TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop) {
        return ThemeReader.getThemeMargins(part.getControlName(c), part.getValue(), TMSchema$State.getValue(part, state), prop.getValue());
    }
    
    synchronized Color getColor(XPStyle$Skin skin, TMSchema$Prop prop, Color fallback) {
        String key = skin.toString() + "." + prop.name();
        TMSchema$Part part = skin.part;
        Color color = (Color)colorMap.get(key);
        if (color == null) {
            color = ThemeReader.getColor(part.getControlName(null), part.getValue(), TMSchema$State.getValue(part, skin.state), prop.getValue());
            if (color != null) {
                color = new ColorUIResource(color);
                colorMap.put(key, color);
            }
        }
        return (color != null) ? color : fallback;
    }
    
    Color getColor(Component c, TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop, Color fallback) {
        return getColor(new XPStyle$Skin(c, part, state), prop, fallback);
    }
    
    synchronized Border getBorder(Component c, TMSchema$Part part) {
        if (part == TMSchema$Part.MENU) {
            if (flatMenus) {
                return new XPStyle$XPFillBorder(this, UIManager.getColor("InternalFrame.borderShadow"), 1);
            } else {
                return null;
            }
        }
        XPStyle$Skin skin = new XPStyle$Skin(c, part, null);
        Border border = (Border)borderMap.get(XPStyle.Skin.access$000(skin));
        if (border == null) {
            String bgType = getTypeEnumName(c, part, null, TMSchema$Prop.BGTYPE);
            if ("borderfill".equalsIgnoreCase(bgType)) {
                int thickness = getInt(c, part, null, TMSchema$Prop.BORDERSIZE, 1);
                Color color = getColor(skin, TMSchema$Prop.BORDERCOLOR, Color.black);
                border = new XPStyle$XPFillBorder(this, color, thickness);
            } else if ("imagefile".equalsIgnoreCase(bgType)) {
                Insets m = getMargin(c, part, null, TMSchema$Prop.SIZINGMARGINS);
                if (m != null) {
                    if (getBoolean(c, part, null, TMSchema$Prop.BORDERONLY)) {
                        border = new XPStyle$XPImageBorder(this, c, part);
                    } else {
                        if (part == TMSchema$Part.TP_BUTTON) {
                            border = new XPStyle$XPEmptyBorder(this, new Insets(3, 3, 3, 3));
                        } else {
                            border = new XPStyle$XPEmptyBorder(this, m);
                        }
                    }
                }
            }
            if (border != null) {
                borderMap.put(XPStyle.Skin.access$000(skin), border);
            }
        }
        return border;
    }
    {
    }
    {
    }
    {
    }
    
    boolean isSkinDefined(Component c, TMSchema$Part part) {
        return (part.getValue() == 0) || ThemeReader.isThemePartDefined(part.getControlName(c), part.getValue(), 0);
    }
    
    synchronized XPStyle$Skin getSkin(Component c, TMSchema$Part part) {
        if (!$assertionsDisabled && !isSkinDefined(c, part)) throw new AssertionError("part " + part + " is not defined");
        return new XPStyle$Skin(c, part, null);
    }
    {
    }
    {
    }
    {
    }
    
    private XPStyle() {
        
        flatMenus = getSysBoolean(TMSchema$Prop.FLATMENUS);
        colorMap = new HashMap();
        borderMap = new HashMap();
    }
    
    private boolean getBoolean(Component c, TMSchema$Part part, TMSchema$State state, TMSchema$Prop prop) {
        return ThemeReader.getBoolean(part.getControlName(c), part.getValue(), TMSchema$State.getValue(part, state), prop.getValue());
    }
    
    private static Dimension getPartSize(TMSchema$Part part, TMSchema$State state) {
        return ThemeReader.getPartSize(part.getControlName(null), part.getValue(), TMSchema$State.getValue(part, state));
    }
    
    private static boolean getSysBoolean(TMSchema$Prop prop) {
        return ThemeReader.getSysBoolean("window", prop.getValue());
    }
}
