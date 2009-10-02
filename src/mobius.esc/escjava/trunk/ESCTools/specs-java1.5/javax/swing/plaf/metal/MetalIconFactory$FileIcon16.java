package javax.swing.plaf.metal;

import javax.swing.*;
import java.awt.*;
import java.awt.image.BufferedImage;
import java.io.Serializable;

public class MetalIconFactory$FileIcon16 implements Icon, Serializable {
    
    public MetalIconFactory$FileIcon16() {
        
    }
    MetalIconFactory$ImageCacher imageCacher;
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        GraphicsConfiguration gc = c.getGraphicsConfiguration();
        if (imageCacher == null) {
            imageCacher = new MetalIconFactory$ImageCacher();
        }
        Image image = imageCacher.getImage(gc);
        if (image == null) {
            if (gc != null) {
                image = gc.createCompatibleImage(getIconWidth(), getIconHeight(), Transparency.BITMASK);
            } else {
                image = new BufferedImage(getIconWidth(), getIconHeight(), BufferedImage.TYPE_INT_ARGB);
            }
            Graphics imageG = image.getGraphics();
            paintMe(c, imageG);
            imageG.dispose();
            imageCacher.cacheImage(image, gc);
        }
        g.drawImage(image, x, y + getShift(), null);
    }
    
    private void paintMe(Component c, Graphics g) {
        int right = MetalIconFactory.access$1600().width - 1;
        int bottom = MetalIconFactory.access$1600().height - 1;
        g.setColor(MetalLookAndFeel.getWindowBackground());
        g.fillRect(4, 2, 9, 12);
        g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        g.drawLine(2, 0, 2, bottom);
        g.drawLine(2, 0, right - 4, 0);
        g.drawLine(2, bottom, right - 1, bottom);
        g.drawLine(right - 1, 6, right - 1, bottom);
        g.drawLine(right - 6, 2, right - 2, 6);
        g.drawLine(right - 5, 1, right - 4, 1);
        g.drawLine(right - 3, 2, right - 3, 3);
        g.drawLine(right - 2, 4, right - 2, 5);
        g.setColor(MetalLookAndFeel.getPrimaryControl());
        g.drawLine(3, 1, 3, bottom - 1);
        g.drawLine(3, 1, right - 6, 1);
        g.drawLine(right - 2, 7, right - 2, bottom - 1);
        g.drawLine(right - 5, 2, right - 3, 4);
        g.drawLine(3, bottom - 1, right - 2, bottom - 1);
    }
    
    public int getShift() {
        return 0;
    }
    
    public int getAdditionalHeight() {
        return 0;
    }
    
    public int getIconWidth() {
        return MetalIconFactory.access$1600().width;
    }
    
    public int getIconHeight() {
        return MetalIconFactory.access$1600().height + getAdditionalHeight();
    }
}
