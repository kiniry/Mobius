package javax.swing.plaf.metal;

import java.awt.*;
import java.awt.image.*;
import javax.swing.*;
import java.io.*;
import java.util.*;

class BumpBuffer {
    static final int IMAGE_SIZE = 64;
    static Dimension imageSize = new Dimension(IMAGE_SIZE, IMAGE_SIZE);
    transient Image image;
    Color topColor;
    Color shadowColor;
    Color backColor;
    private GraphicsConfiguration gc;
    
    public BumpBuffer(GraphicsConfiguration gc, Color aTopColor, Color aShadowColor, Color aBackColor) {
        
        this.gc = gc;
        topColor = aTopColor;
        shadowColor = aShadowColor;
        backColor = aBackColor;
        createImage();
        fillBumpBuffer();
    }
    
    public boolean hasSameConfiguration(GraphicsConfiguration gc, Color aTopColor, Color aShadowColor, Color aBackColor) {
        if (this.gc != null) {
            if (!this.gc.equals(gc)) {
                return false;
            }
        } else if (gc != null) {
            return false;
        }
        return topColor.equals(aTopColor) && shadowColor.equals(aShadowColor) && backColor.equals(aBackColor);
    }
    
    public Image getImage() {
        return image;
    }
    
    public Dimension getImageSize() {
        return imageSize;
    }
    
    private void fillBumpBuffer() {
        Graphics g = image.getGraphics();
        g.setColor(backColor);
        g.fillRect(0, 0, IMAGE_SIZE, IMAGE_SIZE);
        g.setColor(topColor);
        for (int x = 0; x < IMAGE_SIZE; x += 4) {
            for (int y = 0; y < IMAGE_SIZE; y += 4) {
                g.drawLine(x, y, x, y);
                g.drawLine(x + 2, y + 2, x + 2, y + 2);
            }
        }
        g.setColor(shadowColor);
        for (int x = 0; x < IMAGE_SIZE; x += 4) {
            for (int y = 0; y < IMAGE_SIZE; y += 4) {
                g.drawLine(x + 1, y + 1, x + 1, y + 1);
                g.drawLine(x + 3, y + 3, x + 3, y + 3);
            }
        }
        g.dispose();
    }
    
    private void createImage() {
        if (gc != null) {
            image = gc.createCompatibleImage(IMAGE_SIZE, IMAGE_SIZE, (backColor != MetalBumps.ALPHA) ? Transparency.OPAQUE : Transparency.BITMASK);
        } else {
            int[] cmap = {backColor.getRGB(), topColor.getRGB(), shadowColor.getRGB()};
            IndexColorModel icm = new IndexColorModel(8, 3, cmap, 0, false, (backColor == MetalBumps.ALPHA) ? 0 : -1, DataBuffer.TYPE_BYTE);
            image = new BufferedImage(IMAGE_SIZE, IMAGE_SIZE, BufferedImage.TYPE_BYTE_INDEXED, icm);
        }
    }
}
