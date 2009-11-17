package javax.swing.border;

import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Component;
import java.awt.Color;
import javax.swing.Icon;

public class MatteBorder extends EmptyBorder {
    protected Color color;
    protected Icon tileIcon;
    
    public MatteBorder(int top, int left, int bottom, int right, Color matteColor) {
        super(top, left, bottom, right);
        this.color = matteColor;
    }
    
    public MatteBorder(Insets borderInsets, Color matteColor) {
        super(borderInsets);
        this.color = matteColor;
    }
    
    public MatteBorder(int top, int left, int bottom, int right, Icon tileIcon) {
        super(top, left, bottom, right);
        this.tileIcon = tileIcon;
    }
    
    public MatteBorder(Insets borderInsets, Icon tileIcon) {
        super(borderInsets);
        this.tileIcon = tileIcon;
    }
    
    public MatteBorder(Icon tileIcon) {
        this(-1, -1, -1, -1, tileIcon);
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        Insets insets = getBorderInsets(c);
        Color oldColor = g.getColor();
        g.translate(x, y);
        if (tileIcon != null) {
            color = (tileIcon.getIconWidth() == -1) ? Color.gray : null;
        }
        if (color != null) {
            g.setColor(color);
            g.fillRect(0, 0, width - insets.right, insets.top);
            g.fillRect(0, insets.top, insets.left, height - insets.top);
            g.fillRect(insets.left, height - insets.bottom, width - insets.left, insets.bottom);
            g.fillRect(width - insets.right, 0, insets.right, height - insets.bottom);
        } else if (tileIcon != null) {
            int tileW = tileIcon.getIconWidth();
            int tileH = tileIcon.getIconHeight();
            int xpos;
            int ypos;
            int startx;
            int starty;
            Graphics cg;
            cg = g.create();
            cg.setClip(0, 0, width, insets.top);
            for (ypos = 0; insets.top - ypos > 0; ypos += tileH) {
                for (xpos = 0; width - xpos > 0; xpos += tileW) {
                    tileIcon.paintIcon(c, cg, xpos, ypos);
                }
            }
            cg.dispose();
            cg = g.create();
            cg.setClip(0, insets.top, insets.left, height - insets.top);
            starty = insets.top - (insets.top % tileH);
            startx = 0;
            for (ypos = starty; height - ypos > 0; ypos += tileH) {
                for (xpos = startx; insets.left - xpos > 0; xpos += tileW) {
                    tileIcon.paintIcon(c, cg, xpos, ypos);
                }
            }
            cg.dispose();
            cg = g.create();
            cg.setClip(insets.left, height - insets.bottom, width - insets.left, insets.bottom);
            starty = (height - insets.bottom) - ((height - insets.bottom) % tileH);
            startx = insets.left - (insets.left % tileW);
            for (ypos = starty; height - ypos > 0; ypos += tileH) {
                for (xpos = startx; width - xpos > 0; xpos += tileW) {
                    tileIcon.paintIcon(c, cg, xpos, ypos);
                }
            }
            cg.dispose();
            cg = g.create();
            cg.setClip(width - insets.right, insets.top, insets.right, height - insets.top - insets.bottom);
            starty = insets.top - (insets.top % tileH);
            startx = width - insets.right - ((width - insets.right) % tileW);
            for (ypos = starty; height - ypos > 0; ypos += tileH) {
                for (xpos = startx; width - xpos > 0; xpos += tileW) {
                    tileIcon.paintIcon(c, cg, xpos, ypos);
                }
            }
            cg.dispose();
        }
        g.translate(-x, -y);
        g.setColor(oldColor);
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets();
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        return computeInsets(insets);
    }
    
    public Insets getBorderInsets() {
        return computeInsets(new Insets(0, 0, 0, 0));
    }
    
    private Insets computeInsets(Insets insets) {
        if (tileIcon != null && top == -1 && bottom == -1 && left == -1 && right == -1) {
            int w = tileIcon.getIconWidth();
            int h = tileIcon.getIconHeight();
            insets.top = h;
            insets.right = w;
            insets.bottom = h;
            insets.left = w;
        } else {
            insets.left = left;
            insets.top = top;
            insets.right = right;
            insets.bottom = bottom;
        }
        return insets;
    }
    
    public Color getMatteColor() {
        return color;
    }
    
    public Icon getTileIcon() {
        return tileIcon;
    }
    
    public boolean isBorderOpaque() {
        return color != null;
    }
}
