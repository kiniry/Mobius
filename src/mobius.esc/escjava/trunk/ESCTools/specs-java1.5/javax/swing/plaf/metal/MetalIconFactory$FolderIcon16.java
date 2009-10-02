package javax.swing.plaf.metal;

import javax.swing.*;
import java.awt.*;
import java.awt.image.BufferedImage;
import java.io.Serializable;

public class MetalIconFactory$FolderIcon16 implements Icon, Serializable {
    
    public MetalIconFactory$FolderIcon16() {
        
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
        int right = MetalIconFactory.access$1500().width - 1;
        int bottom = MetalIconFactory.access$1500().height - 1;
        g.setColor(MetalLookAndFeel.getPrimaryControlDarkShadow());
        g.drawLine(right - 5, 3, right, 3);
        g.drawLine(right - 6, 4, right, 4);
        g.setColor(MetalLookAndFeel.getPrimaryControl());
        g.fillRect(2, 7, 13, 8);
        g.setColor(MetalLookAndFeel.getPrimaryControlShadow());
        g.drawLine(right - 6, 5, right - 1, 5);
        g.setColor(MetalLookAndFeel.getPrimaryControlInfo());
        g.drawLine(0, 6, 0, bottom);
        g.drawLine(1, 5, right - 7, 5);
        g.drawLine(right - 6, 6, right - 1, 6);
        g.drawLine(right, 5, right, bottom);
        g.drawLine(0, bottom, right, bottom);
        g.setColor(MetalLookAndFeel.getPrimaryControlHighlight());
        g.drawLine(1, 6, 1, bottom - 1);
        g.drawLine(1, 6, right - 7, 6);
        g.drawLine(right - 6, 7, right - 1, 7);
    }
    
    public int getShift() {
        return 0;
    }
    
    public int getAdditionalHeight() {
        return 0;
    }
    
    public int getIconWidth() {
        return MetalIconFactory.access$1500().width;
    }
    
    public int getIconHeight() {
        return MetalIconFactory.access$1500().height + getAdditionalHeight();
    }
}
