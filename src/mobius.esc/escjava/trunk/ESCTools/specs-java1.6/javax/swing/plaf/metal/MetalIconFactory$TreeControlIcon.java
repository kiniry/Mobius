package javax.swing.plaf.metal;

import javax.swing.*;
import java.awt.*;
import java.awt.image.BufferedImage;
import java.io.Serializable;

public class MetalIconFactory$TreeControlIcon implements Icon, Serializable {
    protected boolean isLight;
    
    public MetalIconFactory$TreeControlIcon(boolean isCollapsed) {
        
        isLight = isCollapsed;
    }
    MetalIconFactory$ImageCacher imageCacher;
    transient boolean cachedOrientation = true;
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        GraphicsConfiguration gc = c.getGraphicsConfiguration();
        if (imageCacher == null) {
            imageCacher = new MetalIconFactory$ImageCacher();
        }
        Image image = imageCacher.getImage(gc);
        if (image == null || cachedOrientation != MetalUtils.isLeftToRight(c)) {
            cachedOrientation = MetalUtils.isLeftToRight(c);
            if (gc != null) {
                image = gc.createCompatibleImage(getIconWidth(), getIconHeight(), Transparency.BITMASK);
            } else {
                image = new BufferedImage(getIconWidth(), getIconHeight(), BufferedImage.TYPE_INT_ARGB);
            }
            Graphics imageG = image.getGraphics();
            paintMe(c, imageG, x, y);
            imageG.dispose();
            imageCacher.cacheImage(image, gc);
        }
        if (MetalUtils.isLeftToRight(c)) {
            if (isLight) {
                g.drawImage(image, x + 5, y + 3, x + 18, y + 13, 4, 3, 17, 13, null);
            } else {
                g.drawImage(image, x + 5, y + 3, x + 18, y + 17, 4, 3, 17, 17, null);
            }
        } else {
            if (isLight) {
                g.drawImage(image, x + 3, y + 3, x + 16, y + 13, 4, 3, 17, 13, null);
            } else {
                g.drawImage(image, x + 3, y + 3, x + 16, y + 17, 4, 3, 17, 17, null);
            }
        }
    }
    
    public void paintMe(Component c, Graphics g, int x, int y) {
        g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        int xoff = (MetalUtils.isLeftToRight(c)) ? 0 : 4;
        g.drawLine(xoff + 4, 6, xoff + 4, 9);
        g.drawLine(xoff + 5, 5, xoff + 5, 5);
        g.drawLine(xoff + 6, 4, xoff + 9, 4);
        g.drawLine(xoff + 10, 5, xoff + 10, 5);
        g.drawLine(xoff + 11, 6, xoff + 11, 9);
        g.drawLine(xoff + 10, 10, xoff + 10, 10);
        g.drawLine(xoff + 6, 11, xoff + 9, 11);
        g.drawLine(xoff + 5, 10, xoff + 5, 10);
        g.drawLine(xoff + 7, 7, xoff + 8, 7);
        g.drawLine(xoff + 7, 8, xoff + 8, 8);
        if (isLight) {
            if (MetalUtils.isLeftToRight(c)) {
                g.drawLine(12, 7, 15, 7);
                g.drawLine(12, 8, 15, 8);
            } else {
                g.drawLine(4, 7, 7, 7);
                g.drawLine(4, 8, 7, 8);
            }
        } else {
            g.drawLine(xoff + 7, 12, xoff + 7, 15);
            g.drawLine(xoff + 8, 12, xoff + 8, 15);
        }
        g.setColor(MetalLookAndFeel.getPrimaryControlDarkShadow());
        g.drawLine(xoff + 5, 6, xoff + 5, 9);
        g.drawLine(xoff + 6, 5, xoff + 9, 5);
        g.setColor(MetalLookAndFeel.getPrimaryControlShadow());
        g.drawLine(xoff + 6, 6, xoff + 6, 6);
        g.drawLine(xoff + 9, 6, xoff + 9, 6);
        g.drawLine(xoff + 6, 9, xoff + 6, 9);
        g.drawLine(xoff + 10, 6, xoff + 10, 9);
        g.drawLine(xoff + 6, 10, xoff + 9, 10);
        g.setColor(MetalLookAndFeel.getPrimaryControl());
        g.drawLine(xoff + 6, 7, xoff + 6, 8);
        g.drawLine(xoff + 7, 6, xoff + 8, 6);
        g.drawLine(xoff + 9, 7, xoff + 9, 7);
        g.drawLine(xoff + 7, 9, xoff + 7, 9);
        g.setColor(MetalLookAndFeel.getPrimaryControlHighlight());
        g.drawLine(xoff + 8, 9, xoff + 9, 9);
        g.drawLine(xoff + 9, 8, xoff + 9, 8);
    }
    
    public int getIconWidth() {
        return MetalIconFactory.access$1700().width;
    }
    
    public int getIconHeight() {
        return MetalIconFactory.access$1700().height;
    }
}
