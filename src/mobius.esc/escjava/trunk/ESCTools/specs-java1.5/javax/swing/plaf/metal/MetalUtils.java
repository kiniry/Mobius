package javax.swing.plaf.metal;

import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;
import java.awt.image.*;
import java.lang.ref.*;
import java.util.*;

class MetalUtils {
    
    MetalUtils() {
        
    }
    
    static void drawFlush3DBorder(Graphics g, Rectangle r) {
        drawFlush3DBorder(g, r.x, r.y, r.width, r.height);
    }
    
    static void drawFlush3DBorder(Graphics g, int x, int y, int w, int h) {
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getControlDarkShadow());
        g.drawRect(0, 0, w - 2, h - 2);
        g.setColor(MetalLookAndFeel.getControlHighlight());
        g.drawRect(1, 1, w - 2, h - 2);
        g.setColor(MetalLookAndFeel.getControl());
        g.drawLine(0, h - 1, 1, h - 2);
        g.drawLine(w - 1, 0, w - 2, 1);
        g.translate(-x, -y);
    }
    
    static void drawPressed3DBorder(Graphics g, Rectangle r) {
        drawPressed3DBorder(g, r.x, r.y, r.width, r.height);
    }
    
    static void drawDisabledBorder(Graphics g, int x, int y, int w, int h) {
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getControlShadow());
        g.drawRect(0, 0, w - 1, h - 1);
        g.translate(-x, -y);
    }
    
    static void drawPressed3DBorder(Graphics g, int x, int y, int w, int h) {
        g.translate(x, y);
        drawFlush3DBorder(g, 0, 0, w, h);
        g.setColor(MetalLookAndFeel.getControlShadow());
        g.drawLine(1, 1, 1, h - 2);
        g.drawLine(1, 1, w - 2, 1);
        g.translate(-x, -y);
    }
    
    static void drawDark3DBorder(Graphics g, Rectangle r) {
        drawDark3DBorder(g, r.x, r.y, r.width, r.height);
    }
    
    static void drawDark3DBorder(Graphics g, int x, int y, int w, int h) {
        g.translate(x, y);
        drawFlush3DBorder(g, 0, 0, w, h);
        g.setColor(MetalLookAndFeel.getControl());
        g.drawLine(1, 1, 1, h - 2);
        g.drawLine(1, 1, w - 2, 1);
        g.setColor(MetalLookAndFeel.getControlShadow());
        g.drawLine(1, h - 2, 1, h - 2);
        g.drawLine(w - 2, 1, w - 2, 1);
        g.translate(-x, -y);
    }
    
    static void drawButtonBorder(Graphics g, int x, int y, int w, int h, boolean active) {
        if (active) {
            drawActiveButtonBorder(g, x, y, w, h);
        } else {
            drawFlush3DBorder(g, x, y, w, h);
        }
    }
    
    static void drawActiveButtonBorder(Graphics g, int x, int y, int w, int h) {
        drawFlush3DBorder(g, x, y, w, h);
        g.setColor(MetalLookAndFeel.getPrimaryControl());
        g.drawLine(x + 1, y + 1, x + 1, h - 3);
        g.drawLine(x + 1, y + 1, w - 3, x + 1);
        g.setColor(MetalLookAndFeel.getPrimaryControlDarkShadow());
        g.drawLine(x + 2, h - 2, w - 2, h - 2);
        g.drawLine(w - 2, y + 2, w - 2, h - 2);
    }
    
    static void drawDefaultButtonBorder(Graphics g, int x, int y, int w, int h, boolean active) {
        drawButtonBorder(g, x + 1, y + 1, w - 1, h - 1, active);
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getControlDarkShadow());
        g.drawRect(0, 0, w - 3, h - 3);
        g.drawLine(w - 2, 0, w - 2, 0);
        g.drawLine(0, h - 2, 0, h - 2);
        g.translate(-x, -y);
    }
    
    static void drawDefaultButtonPressedBorder(Graphics g, int x, int y, int w, int h) {
        drawPressed3DBorder(g, x + 1, y + 1, w - 1, h - 1);
        g.translate(x, y);
        g.setColor(MetalLookAndFeel.getControlDarkShadow());
        g.drawRect(0, 0, w - 3, h - 3);
        g.drawLine(w - 2, 0, w - 2, 0);
        g.drawLine(0, h - 2, 0, h - 2);
        g.setColor(MetalLookAndFeel.getControl());
        g.drawLine(w - 1, 0, w - 1, 0);
        g.drawLine(0, h - 1, 0, h - 1);
        g.translate(-x, -y);
    }
    
    static boolean isLeftToRight(Component c) {
        return c.getComponentOrientation().isLeftToRight();
    }
    
    static int getInt(Object key, int defaultValue) {
        Object value = UIManager.get(key);
        if (value instanceof Integer) {
            return ((Integer)(Integer)value).intValue();
        }
        if (value instanceof String) {
            try {
                return Integer.parseInt((String)(String)value);
            } catch (NumberFormatException nfe) {
            }
        }
        return defaultValue;
    }
    
    static boolean drawGradient(Component c, Graphics g, String key, int x, int y, int w, int h, boolean vertical) {
        java.util.List gradient = (java.util.List)(.java.util.List)UIManager.get(key);
        if (gradient == null || !(g instanceof Graphics2D)) {
            return false;
        }
        if (w <= 0 || h <= 0) {
            return true;
        }
        MetalUtils$GradientPainter.INSTANCE.paint(c, (Graphics2D)(Graphics2D)g, gradient, x, y, w, h, vertical);
        return true;
    }
    {
    }
    
    static boolean isToolBarButton(JComponent c) {
        return (c.getParent() instanceof JToolBar);
    }
    
    static Icon getOceanToolBarIcon(Image i) {
        ImageProducer prod = new FilteredImageSource(i.getSource(), new MetalUtils$OceanToolBarImageFilter());
        return new IconUIResource(new ImageIcon(Toolkit.getDefaultToolkit().createImage(prod)));
    }
    
    static Icon getOceanDisabledButtonIcon(Image image) {
        Object[] range = (Object[])(Object[])UIManager.get("Button.disabledGrayRange");
        int min = 180;
        int max = 215;
        if (range != null) {
            min = ((Integer)(Integer)range[0]).intValue();
            max = ((Integer)(Integer)range[1]).intValue();
        }
        ImageProducer prod = new FilteredImageSource(image.getSource(), new MetalUtils$OceanDisabledButtonImageFilter(min, max));
        return new IconUIResource(new ImageIcon(Toolkit.getDefaultToolkit().createImage(prod)));
    }
    {
    }
    {
    }
}
