package javax.swing.plaf.basic;

import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Color;
import javax.swing.*;
import javax.swing.plaf.UIResource;

public class BasicArrowButton extends JButton implements SwingConstants {
    protected int direction;
    private Color shadow;
    private Color darkShadow;
    private Color highlight;
    
    public BasicArrowButton(int direction, Color background, Color shadow, Color darkShadow, Color highlight) {
        
        setRequestFocusEnabled(false);
        setDirection(direction);
        setBackground(background);
        this.shadow = shadow;
        this.darkShadow = darkShadow;
        this.highlight = highlight;
    }
    
    public BasicArrowButton(int direction) {
        this(direction, UIManager.getColor("control"), UIManager.getColor("controlShadow"), UIManager.getColor("controlDkShadow"), UIManager.getColor("controlLtHighlight"));
    }
    
    public int getDirection() {
        return direction;
    }
    
    public void setDirection(int dir) {
        direction = dir;
    }
    
    public void paint(Graphics g) {
        Color origColor;
        boolean isPressed;
        boolean isEnabled;
        int w;
        int h;
        int size;
        w = getSize().width;
        h = getSize().height;
        origColor = g.getColor();
        isPressed = getModel().isPressed();
        isEnabled = isEnabled();
        g.setColor(getBackground());
        g.fillRect(1, 1, w - 2, h - 2);
        if (getBorder() != null && !(getBorder() instanceof UIResource)) {
            paintBorder(g);
        } else if (isPressed) {
            g.setColor(shadow);
            g.drawRect(0, 0, w - 1, h - 1);
        } else {
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
        if (h < 5 || w < 5) {
            g.setColor(origColor);
            return;
        }
        if (isPressed) {
            g.translate(1, 1);
        }
        size = Math.min((h - 4) / 3, (w - 4) / 3);
        size = Math.max(size, 2);
        paintTriangle(g, (w - size) / 2, (h - size) / 2, size, direction, isEnabled);
        if (isPressed) {
            g.translate(-1, -1);
        }
        g.setColor(origColor);
    }
    
    public Dimension getPreferredSize() {
        return new Dimension(16, 16);
    }
    
    public Dimension getMinimumSize() {
        return new Dimension(5, 5);
    }
    
    public Dimension getMaximumSize() {
        return new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE);
    }
    
    public boolean isFocusTraversable() {
        return false;
    }
    
    public void paintTriangle(Graphics g, int x, int y, int size, int direction, boolean isEnabled) {
        Color oldColor = g.getColor();
        int mid;
        int i;
        int j;
        j = 0;
        size = Math.max(size, 2);
        mid = (size / 2) - 1;
        g.translate(x, y);
        if (isEnabled) g.setColor(darkShadow); else g.setColor(shadow);
        switch (direction) {
        case NORTH: 
            for (i = 0; i < size; i++) {
                g.drawLine(mid - i, i, mid + i, i);
            }
            if (!isEnabled) {
                g.setColor(highlight);
                g.drawLine(mid - i + 2, i, mid + i, i);
            }
            break;
        
        case SOUTH: 
            if (!isEnabled) {
                g.translate(1, 1);
                g.setColor(highlight);
                for (i = size - 1; i >= 0; i--) {
                    g.drawLine(mid - i, j, mid + i, j);
                    j++;
                }
                g.translate(-1, -1);
                g.setColor(shadow);
            }
            j = 0;
            for (i = size - 1; i >= 0; i--) {
                g.drawLine(mid - i, j, mid + i, j);
                j++;
            }
            break;
        
        case WEST: 
            for (i = 0; i < size; i++) {
                g.drawLine(i, mid - i, i, mid + i);
            }
            if (!isEnabled) {
                g.setColor(highlight);
                g.drawLine(i, mid - i + 2, i, mid + i);
            }
            break;
        
        case EAST: 
            if (!isEnabled) {
                g.translate(1, 1);
                g.setColor(highlight);
                for (i = size - 1; i >= 0; i--) {
                    g.drawLine(j, mid - i, j, mid + i);
                    j++;
                }
                g.translate(-1, -1);
                g.setColor(shadow);
            }
            j = 0;
            for (i = size - 1; i >= 0; i--) {
                g.drawLine(j, mid - i, j, mid + i);
                j++;
            }
            break;
        
        }
        g.translate(-x, -y);
        g.setColor(oldColor);
    }
}
