package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$OceanVerticalSliderThumbIcon extends CachedPainter implements Icon, Serializable, UIResource {
    private static Polygon LTR_THUMB_SHAPE;
    private static Polygon RTL_THUMB_SHAPE;
    static {
        LTR_THUMB_SHAPE = new Polygon(new int[]{0, 8, 15, 8, 0}, new int[]{0, 0, 7, 14, 14}, 5);
        RTL_THUMB_SHAPE = new Polygon(new int[]{15, 15, 7, 0, 7}, new int[]{0, 14, 14, 7, 0}, 5);
    }
    
    MetalIconFactory$OceanVerticalSliderThumbIcon() {
        super(3);
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        if (!(g instanceof Graphics2D)) {
            return;
        }
        paint(c, g, x, y, getIconWidth(), getIconHeight(), new Object[]{Boolean.valueOf(MetalUtils.isLeftToRight(c)), Boolean.valueOf(c.hasFocus()), Boolean.valueOf(c.isEnabled()), MetalLookAndFeel.getCurrentTheme()});
    }
    
    protected void paintToImage(Component c, Graphics g2, int w, int h, Object[] args) {
        Graphics2D g = (Graphics2D)(Graphics2D)g2;
        boolean leftToRight = ((Boolean)(Boolean)args[0]).booleanValue();
        boolean hasFocus = ((Boolean)(Boolean)args[1]).booleanValue();
        boolean enabled = ((Boolean)(Boolean)args[2]).booleanValue();
        Rectangle clip = g.getClipBounds();
        if (leftToRight) {
            g.clip(LTR_THUMB_SHAPE);
        } else {
            g.clip(RTL_THUMB_SHAPE);
        }
        if (!enabled) {
            g.setColor(MetalLookAndFeel.getControl());
            g.fillRect(1, 1, 14, 14);
        } else if (hasFocus) {
            MetalUtils.drawGradient(c, g, "Slider.focusGradient", 1, 1, 14, 14, false);
        } else {
            MetalUtils.drawGradient(c, g, "Slider.gradient", 1, 1, 14, 14, false);
        }
        g.setClip(clip);
        if (hasFocus) {
            g.setColor(MetalLookAndFeel.getPrimaryControlDarkShadow());
        } else {
            g.setColor(enabled ? MetalLookAndFeel.getPrimaryControlInfo() : MetalLookAndFeel.getControlDarkShadow());
        }
        if (leftToRight) {
            g.drawLine(1, 0, 8, 0);
            g.drawLine(0, 1, 0, 13);
            g.drawLine(1, 14, 8, 14);
            g.drawLine(9, 1, 15, 7);
            g.drawLine(9, 13, 15, 7);
        } else {
            g.drawLine(7, 0, 14, 0);
            g.drawLine(15, 1, 15, 13);
            g.drawLine(7, 14, 14, 14);
            g.drawLine(0, 7, 6, 1);
            g.drawLine(0, 7, 6, 13);
        }
        if (hasFocus && enabled) {
            g.setColor(MetalLookAndFeel.getPrimaryControl());
            if (leftToRight) {
                g.drawLine(1, 1, 8, 1);
                g.drawLine(1, 1, 1, 13);
                g.drawLine(1, 13, 8, 13);
                g.drawLine(9, 2, 14, 7);
                g.drawLine(9, 12, 14, 7);
            } else {
                g.drawLine(7, 1, 14, 1);
                g.drawLine(14, 1, 14, 13);
                g.drawLine(7, 13, 14, 13);
                g.drawLine(1, 7, 7, 1);
                g.drawLine(1, 7, 7, 13);
            }
        }
    }
    
    public int getIconWidth() {
        return 16;
    }
    
    public int getIconHeight() {
        return 15;
    }
    
    protected Image createImage(Component c, int w, int h, GraphicsConfiguration config) {
        return config.createCompatibleImage(w, h, Transparency.BITMASK);
    }
}
