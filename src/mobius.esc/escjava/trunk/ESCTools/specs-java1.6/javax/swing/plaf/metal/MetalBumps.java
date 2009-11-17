package javax.swing.plaf.metal;

import java.awt.*;
import java.awt.image.*;
import javax.swing.*;
import java.io.*;
import java.util.*;

class MetalBumps implements Icon {
    static final Color ALPHA = new Color(0, 0, 0, 0);
    protected int xBumps;
    protected int yBumps;
    protected Color topColor;
    protected Color shadowColor;
    protected Color backColor;
    protected static Vector buffers = new Vector();
    protected BumpBuffer buffer;
    
    public MetalBumps(Dimension bumpArea) {
        this(bumpArea.width, bumpArea.height);
    }
    
    public MetalBumps(int width, int height) {
        this(width, height, MetalLookAndFeel.getPrimaryControlHighlight(), MetalLookAndFeel.getPrimaryControlDarkShadow(), MetalLookAndFeel.getPrimaryControlShadow());
    }
    
    public MetalBumps(int width, int height, Color newTopColor, Color newShadowColor, Color newBackColor) {
        
        setBumpArea(width, height);
        setBumpColors(newTopColor, newShadowColor, newBackColor);
    }
    
    private BumpBuffer getBuffer(GraphicsConfiguration gc, Color aTopColor, Color aShadowColor, Color aBackColor) {
        if (buffer != null && buffer.hasSameConfiguration(gc, aTopColor, aShadowColor, aBackColor)) {
            return buffer;
        }
        BumpBuffer result = null;
        Enumeration elements = buffers.elements();
        while (elements.hasMoreElements()) {
            BumpBuffer aBuffer = (BumpBuffer)(BumpBuffer)elements.nextElement();
            if (aBuffer.hasSameConfiguration(gc, aTopColor, aShadowColor, aBackColor)) {
                result = aBuffer;
                break;
            }
        }
        if (result == null) {
            result = new BumpBuffer(gc, topColor, shadowColor, backColor);
            buffers.addElement(result);
        }
        return result;
    }
    
    public void setBumpArea(Dimension bumpArea) {
        setBumpArea(bumpArea.width, bumpArea.height);
    }
    
    public void setBumpArea(int width, int height) {
        xBumps = width / 2;
        yBumps = height / 2;
    }
    
    public void setBumpColors(Color newTopColor, Color newShadowColor, Color newBackColor) {
        topColor = newTopColor;
        shadowColor = newShadowColor;
        if (newBackColor == null) {
            backColor = ALPHA;
        } else {
            backColor = newBackColor;
        }
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        GraphicsConfiguration gc = (g instanceof Graphics2D) ? (GraphicsConfiguration)((Graphics2D)(Graphics2D)g).getDeviceConfiguration() : null;
        buffer = getBuffer(gc, topColor, shadowColor, backColor);
        int bufferWidth = buffer.getImageSize().width;
        int bufferHeight = buffer.getImageSize().height;
        int iconWidth = getIconWidth();
        int iconHeight = getIconHeight();
        int x2 = x + iconWidth;
        int y2 = y + iconHeight;
        int savex = x;
        while (y < y2) {
            int h = Math.min(y2 - y, bufferHeight);
            for (x = savex; x < x2; x += bufferWidth) {
                int w = Math.min(x2 - x, bufferWidth);
                g.drawImage(buffer.getImage(), x, y, x + w, y + h, 0, 0, w, h, null);
            }
            y += bufferHeight;
        }
    }
    
    public int getIconWidth() {
        return xBumps * 2;
    }
    
    public int getIconHeight() {
        return yBumps * 2;
    }
}
