package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$OceanHorizontalSliderThumbIcon extends CachedPainter implements Icon, Serializable, UIResource {
    private static Polygon THUMB_SHAPE;
    static {
        THUMB_SHAPE = new Polygon(new int[]{0, 14, 14, 7, 0}, new int[]{0, 0, 8, 15, 8}, 5);
    }
    
    MetalIconFactory$OceanHorizontalSliderThumbIcon() {
        super(3);
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        if (!(g instanceof Graphics2D)) {
            return;
        }
        paint(c, g, x, y, getIconWidth(), getIconHeight(), new Object[]{Boolean.valueOf(c.hasFocus()), Boolean.valueOf(c.isEnabled()), MetalLookAndFeel.getCurrentTheme()});
    }
    
    protected Image createImage(Component c, int w, int h, GraphicsConfiguration config) {
        return config.createCompatibleImage(w, h, Transparency.BITMASK);
    }
    
    protected void paintToImage(Component c, Graphics g2, int w, int h, Object[] args) {
        Graphics2D g = (Graphics2D)(Graphics2D)g2;
        boolean hasFocus = ((Boolean)(Boolean)args[0]).booleanValue();
        boolean enabled = ((Boolean)(Boolean)args[1]).booleanValue();
        Rectangle clip = g.getClipBounds();
        g.clip(THUMB_SHAPE);
        if (!enabled) {
            g.setColor(MetalLookAndFeel.getControl());
            g.fillRect(1, 1, 13, 14);
        } else if (hasFocus) {
            MetalUtils.drawGradient(c, g, "Slider.focusGradient", 1, 1, 13, 14, true);
        } else {
            MetalUtils.drawGradient(c, g, "Slider.gradient", 1, 1, 13, 14, true);
        }
        g.setClip(clip);
        if (hasFocus) {
            g.setColor(MetalLookAndFeel.getPrimaryControlDarkShadow());
        } else {
            g.setColor(enabled ? MetalLookAndFeel.getPrimaryControlInfo() : MetalLookAndFeel.getControlDarkShadow());
        }
        g.drawLine(1, 0, 13, 0);
        g.drawLine(0, 1, 0, 8);
        g.drawLine(14, 1, 14, 8);
        g.drawLine(1, 9, 7, 15);
        g.drawLine(7, 15, 14, 8);
        if (hasFocus && enabled) {
            g.setColor(MetalLookAndFeel.getPrimaryControl());
            g.fillRect(1, 1, 13, 1);
            g.fillRect(1, 2, 1, 7);
            g.fillRect(13, 2, 1, 7);
            g.drawLine(2, 9, 7, 14);
            g.drawLine(8, 13, 12, 9);
        }
    }
    
    public int getIconWidth() {
        return 15;
    }
    
    public int getIconHeight() {
        return 16;
    }
}
