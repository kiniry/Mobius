package javax.swing.plaf.basic;

import javax.swing.*;
import java.awt.Component;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Rectangle;
import com.sun.java.swing.SwingUtilities2;

public class BasicGraphicsUtils {
    
    public BasicGraphicsUtils() {
        
    }
    private static final Insets GROOVE_INSETS = new Insets(2, 2, 2, 2);
    private static final Insets ETCHED_INSETS = new Insets(2, 2, 2, 2);
    
    public static void drawEtchedRect(Graphics g, int x, int y, int w, int h, Color shadow, Color darkShadow, Color highlight, Color lightHighlight) {
        Color oldColor = g.getColor();
        g.translate(x, y);
        g.setColor(shadow);
        g.drawLine(0, 0, w - 1, 0);
        g.drawLine(0, 1, 0, h - 2);
        g.setColor(darkShadow);
        g.drawLine(1, 1, w - 3, 1);
        g.drawLine(1, 2, 1, h - 3);
        g.setColor(lightHighlight);
        g.drawLine(w - 1, 0, w - 1, h - 1);
        g.drawLine(0, h - 1, w - 1, h - 1);
        g.setColor(highlight);
        g.drawLine(w - 2, 1, w - 2, h - 3);
        g.drawLine(1, h - 2, w - 2, h - 2);
        g.translate(-x, -y);
        g.setColor(oldColor);
    }
    
    public static Insets getEtchedInsets() {
        return ETCHED_INSETS;
    }
    
    public static void drawGroove(Graphics g, int x, int y, int w, int h, Color shadow, Color highlight) {
        Color oldColor = g.getColor();
        g.translate(x, y);
        g.setColor(shadow);
        g.drawRect(0, 0, w - 2, h - 2);
        g.setColor(highlight);
        g.drawLine(1, h - 3, 1, 1);
        g.drawLine(1, 1, w - 3, 1);
        g.drawLine(0, h - 1, w - 1, h - 1);
        g.drawLine(w - 1, h - 1, w - 1, 0);
        g.translate(-x, -y);
        g.setColor(oldColor);
    }
    
    public static Insets getGrooveInsets() {
        return GROOVE_INSETS;
    }
    
    public static void drawBezel(Graphics g, int x, int y, int w, int h, boolean isPressed, boolean isDefault, Color shadow, Color darkShadow, Color highlight, Color lightHighlight) {
        Color oldColor = g.getColor();
        g.translate(x, y);
        if (isPressed && isDefault) {
            g.setColor(darkShadow);
            g.drawRect(0, 0, w - 1, h - 1);
            g.setColor(shadow);
            g.drawRect(1, 1, w - 3, h - 3);
        } else if (isPressed) {
            drawLoweredBezel(g, x, y, w, h, shadow, darkShadow, highlight, lightHighlight);
        } else if (isDefault) {
            g.setColor(darkShadow);
            g.drawRect(0, 0, w - 1, h - 1);
            g.setColor(lightHighlight);
            g.drawLine(1, 1, 1, h - 3);
            g.drawLine(2, 1, w - 3, 1);
            g.setColor(highlight);
            g.drawLine(2, 2, 2, h - 4);
            g.drawLine(3, 2, w - 4, 2);
            g.setColor(shadow);
            g.drawLine(2, h - 3, w - 3, h - 3);
            g.drawLine(w - 3, 2, w - 3, h - 4);
            g.setColor(darkShadow);
            g.drawLine(1, h - 2, w - 2, h - 2);
            g.drawLine(w - 2, h - 2, w - 2, 1);
        } else {
            g.setColor(lightHighlight);
            g.drawLine(0, 0, 0, h - 1);
            g.drawLine(1, 0, w - 2, 0);
            g.setColor(highlight);
            g.drawLine(1, 1, 1, h - 3);
            g.drawLine(2, 1, w - 3, 1);
            g.setColor(shadow);
            g.drawLine(1, h - 2, w - 2, h - 2);
            g.drawLine(w - 2, 1, w - 2, h - 3);
            g.setColor(darkShadow);
            g.drawLine(0, h - 1, w - 1, h - 1);
            g.drawLine(w - 1, h - 1, w - 1, 0);
        }
        g.translate(-x, -y);
        g.setColor(oldColor);
    }
    
    public static void drawLoweredBezel(Graphics g, int x, int y, int w, int h, Color shadow, Color darkShadow, Color highlight, Color lightHighlight) {
        g.setColor(darkShadow);
        g.drawLine(0, 0, 0, h - 1);
        g.drawLine(1, 0, w - 2, 0);
        g.setColor(shadow);
        g.drawLine(1, 1, 1, h - 2);
        g.drawLine(1, 1, w - 3, 1);
        g.setColor(lightHighlight);
        g.drawLine(0, h - 1, w - 1, h - 1);
        g.drawLine(w - 1, h - 1, w - 1, 0);
        g.setColor(highlight);
        g.drawLine(1, h - 2, w - 2, h - 2);
        g.drawLine(w - 2, h - 2, w - 2, 1);
    }
    
    public static void drawString(Graphics g, String text, int underlinedChar, int x, int y) {
        int index = -1;
        if (underlinedChar != '\000') {
            char uc = Character.toUpperCase((char)underlinedChar);
            char lc = Character.toLowerCase((char)underlinedChar);
            int uci = text.indexOf(uc);
            int lci = text.indexOf(lc);
            if (uci == -1) {
                index = lci;
            } else if (lci == -1) {
                index = uci;
            } else {
                index = (lci < uci) ? lci : uci;
            }
        }
        drawStringUnderlineCharAt(g, text, index, x, y);
    }
    
    public static void drawStringUnderlineCharAt(Graphics g, String text, int underlinedIndex, int x, int y) {
        SwingUtilities2.drawStringUnderlineCharAt(null, g, text, underlinedIndex, x, y);
    }
    
    public static void drawDashedRect(Graphics g, int x, int y, int width, int height) {
        int vx;
        int vy;
        for (vx = x; vx < (x + width); vx += 2) {
            g.fillRect(vx, y, 1, 1);
            g.fillRect(vx, y + height - 1, 1, 1);
        }
        for (vy = y; vy < (y + height); vy += 2) {
            g.fillRect(x, vy, 1, 1);
            g.fillRect(x + width - 1, vy, 1, 1);
        }
    }
    
    public static Dimension getPreferredButtonSize(AbstractButton b, int textIconGap) {
        if (b.getComponentCount() > 0) {
            return null;
        }
        Icon icon = (Icon)b.getIcon();
        String text = b.getText();
        Font font = b.getFont();
        FontMetrics fm = b.getFontMetrics(font);
        Rectangle iconR = new Rectangle();
        Rectangle textR = new Rectangle();
        Rectangle viewR = new Rectangle(Short.MAX_VALUE, Short.MAX_VALUE);
        SwingUtilities.layoutCompoundLabel((JComponent)b, fm, text, icon, b.getVerticalAlignment(), b.getHorizontalAlignment(), b.getVerticalTextPosition(), b.getHorizontalTextPosition(), viewR, iconR, textR, (text == null ? 0 : textIconGap));
        Rectangle r = iconR.union(textR);
        Insets insets = b.getInsets();
        r.width += insets.left + insets.right;
        r.height += insets.top + insets.bottom;
        return r.getSize();
    }
    
    static boolean isLeftToRight(Component c) {
        return c.getComponentOrientation().isLeftToRight();
    }
}
