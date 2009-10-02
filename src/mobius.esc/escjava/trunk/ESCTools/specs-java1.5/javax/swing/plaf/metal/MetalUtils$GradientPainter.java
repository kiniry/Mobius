package javax.swing.plaf.metal;

import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;
import java.awt.image.*;
import java.lang.ref.*;
import java.util.*;

class MetalUtils$GradientPainter extends CachedPainter {
    public static final MetalUtils$GradientPainter INSTANCE = new MetalUtils$GradientPainter(8);
    private static final int IMAGE_SIZE = 64;
    private int w;
    private int h;
    
    MetalUtils$GradientPainter(int count) {
        super(count);
    }
    
    public void paint(Component c, Graphics2D g, java.util.List gradient, int x, int y, int w, int h, boolean isVertical) {
        int imageWidth;
        int imageHeight;
        if (isVertical) {
            imageWidth = IMAGE_SIZE;
            imageHeight = h;
        } else {
            imageWidth = w;
            imageHeight = IMAGE_SIZE;
        }
        synchronized (c.getTreeLock()) {
            this.w = w;
            this.h = h;
            paint(c, g, x, y, imageWidth, imageHeight, new Object[]{gradient, Boolean.valueOf(isVertical)});
        }
    }
    
    protected void paintToImage(Component c, Graphics g, int w, int h, Object[] args) {
        Graphics2D g2 = (Graphics2D)(Graphics2D)g;
        java.util.List gradient = (java.util.List)(.java.util.List)args[0];
        boolean isVertical = ((Boolean)(Boolean)args[1]).booleanValue();
        if (isVertical) {
            drawVerticalGradient(g2, ((Number)(Number)gradient.get(0)).floatValue(), ((Number)(Number)gradient.get(1)).floatValue(), (Color)(Color)gradient.get(2), (Color)(Color)gradient.get(3), (Color)(Color)gradient.get(4), w, h);
        } else {
            drawHorizontalGradient(g2, ((Number)(Number)gradient.get(0)).floatValue(), ((Number)(Number)gradient.get(1)).floatValue(), (Color)(Color)gradient.get(2), (Color)(Color)gradient.get(3), (Color)(Color)gradient.get(4), w, h);
        }
    }
    
    protected void paintImage(Component c, Graphics g, int x, int y, int imageW, int imageH, Image image, Object[] args) {
        boolean isVertical = ((Boolean)(Boolean)args[1]).booleanValue();
        g.translate(x, y);
        if (isVertical) {
            for (int counter = 0; counter < w; counter += IMAGE_SIZE) {
                int tileSize = Math.min(IMAGE_SIZE, w - counter);
                g.drawImage(image, counter, 0, counter + tileSize, h, 0, 0, tileSize, h, null);
            }
        } else {
            for (int counter = 0; counter < h; counter += IMAGE_SIZE) {
                int tileSize = Math.min(IMAGE_SIZE, h - counter);
                g.drawImage(image, 0, counter, w, counter + tileSize, 0, 0, w, tileSize, null);
            }
        }
        g.translate(-x, -y);
    }
    
    private void drawVerticalGradient(Graphics2D g, float ratio1, float ratio2, Color c1, Color c2, Color c3, int w, int h) {
        int mid = (int)(ratio1 * h);
        int mid2 = (int)(ratio2 * h);
        if (mid > 0) {
            g.setPaint(getGradient((float)0, (float)0, c1, (float)0, (float)mid, c2));
            g.fillRect(0, 0, w, mid);
        }
        if (mid2 > 0) {
            g.setColor(c2);
            g.fillRect(0, mid, w, mid2);
        }
        if (mid > 0) {
            g.setPaint(getGradient((float)0, (float)mid + mid2, c2, (float)0, (float)mid * 2 + mid2, c1));
            g.fillRect(0, mid + mid2, w, mid);
        }
        if (h - mid * 2 - mid2 > 0) {
            g.setPaint(getGradient((float)0, (float)mid * 2 + mid2, c1, (float)0, (float)h, c3));
            g.fillRect(0, mid * 2 + mid2, w, h - mid * 2 - mid2);
        }
    }
    
    private void drawHorizontalGradient(Graphics2D g, float ratio1, float ratio2, Color c1, Color c2, Color c3, int w, int h) {
        int mid = (int)(ratio1 * w);
        int mid2 = (int)(ratio2 * w);
        if (mid > 0) {
            g.setPaint(getGradient((float)0, (float)0, c1, (float)mid, (float)0, c2));
            g.fillRect(0, 0, mid, h);
        }
        if (mid2 > 0) {
            g.setColor(c2);
            g.fillRect(mid, 0, mid2, h);
        }
        if (mid > 0) {
            g.setPaint(getGradient((float)mid + mid2, (float)0, c2, (float)mid * 2 + mid2, (float)0, c1));
            g.fillRect(mid + mid2, 0, mid, h);
        }
        if (w - mid * 2 - mid2 > 0) {
            g.setPaint(getGradient((float)mid * 2 + mid2, (float)0, c1, w, (float)0, c3));
            g.fillRect(mid * 2 + mid2, 0, w - mid * 2 - mid2, h);
        }
    }
    
    private GradientPaint getGradient(float x1, float y1, Color c1, float x2, float y2, Color c2) {
        return new GradientPaint(x1, y1, c1, x2, y2, c2, true);
    }
}
