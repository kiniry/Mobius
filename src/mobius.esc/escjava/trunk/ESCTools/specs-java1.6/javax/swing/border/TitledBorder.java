package javax.swing.border;

import com.sun.java.swing.SwingUtilities2;
import java.awt.Graphics;
import java.awt.Insets;
import java.awt.Rectangle;
import java.awt.Color;
import java.awt.Font;
import java.awt.FontMetrics;
import java.awt.Point;
import java.awt.Component;
import java.awt.Dimension;
import javax.swing.JComponent;
import javax.swing.UIManager;

public class TitledBorder extends AbstractBorder {
    protected String title;
    protected Border border;
    protected int titlePosition;
    protected int titleJustification;
    protected Font titleFont;
    protected Color titleColor;
    private Point textLoc = new Point();
    public static final int DEFAULT_POSITION = 0;
    public static final int ABOVE_TOP = 1;
    public static final int TOP = 2;
    public static final int BELOW_TOP = 3;
    public static final int ABOVE_BOTTOM = 4;
    public static final int BOTTOM = 5;
    public static final int BELOW_BOTTOM = 6;
    public static final int DEFAULT_JUSTIFICATION = 0;
    public static final int LEFT = 1;
    public static final int CENTER = 2;
    public static final int RIGHT = 3;
    public static final int LEADING = 4;
    public static final int TRAILING = 5;
    protected static final int EDGE_SPACING = 2;
    protected static final int TEXT_SPACING = 2;
    protected static final int TEXT_INSET_H = 5;
    
    public TitledBorder(String title) {
        this(null, title, LEADING, TOP, null, null);
    }
    
    public TitledBorder(Border border) {
        this(border, "", LEADING, TOP, null, null);
    }
    
    public TitledBorder(Border border, String title) {
        this(border, title, LEADING, TOP, null, null);
    }
    
    public TitledBorder(Border border, String title, int titleJustification, int titlePosition) {
        this(border, title, titleJustification, titlePosition, null, null);
    }
    
    public TitledBorder(Border border, String title, int titleJustification, int titlePosition, Font titleFont) {
        this(border, title, titleJustification, titlePosition, titleFont, null);
    }
    
    public TitledBorder(Border border, String title, int titleJustification, int titlePosition, Font titleFont, Color titleColor) {
        
        this.title = title;
        this.border = border;
        this.titleFont = titleFont;
        this.titleColor = titleColor;
        setTitleJustification(titleJustification);
        setTitlePosition(titlePosition);
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        Border border = getBorder();
        if (getTitle() == null || getTitle().equals("")) {
            if (border != null) {
                border.paintBorder(c, g, x, y, width, height);
            }
            return;
        }
        Rectangle grooveRect = new Rectangle(x + EDGE_SPACING, y + EDGE_SPACING, width - (EDGE_SPACING * 2), height - (EDGE_SPACING * 2));
        Font font = g.getFont();
        Color color = g.getColor();
        g.setFont(getFont(c));
        JComponent jc = (c instanceof JComponent) ? (JComponent)(JComponent)c : null;
        FontMetrics fm = SwingUtilities2.getFontMetrics(jc, g);
        int fontHeight = fm.getHeight();
        int descent = fm.getDescent();
        int ascent = fm.getAscent();
        int diff;
        int stringWidth = SwingUtilities2.stringWidth(jc, fm, getTitle());
        Insets insets;
        if (border != null) {
            insets = border.getBorderInsets(c);
        } else {
            insets = new Insets(0, 0, 0, 0);
        }
        int titlePos = getTitlePosition();
        switch (titlePos) {
        case ABOVE_TOP: 
            diff = ascent + descent + (Math.max(EDGE_SPACING, TEXT_SPACING * 2) - EDGE_SPACING);
            grooveRect.y += diff;
            grooveRect.height -= diff;
            textLoc.y = grooveRect.y - (descent + TEXT_SPACING);
            break;
        
        case TOP: 
        
        case DEFAULT_POSITION: 
            diff = Math.max(0, ((ascent / 2) + TEXT_SPACING) - EDGE_SPACING);
            grooveRect.y += diff;
            grooveRect.height -= diff;
            textLoc.y = (grooveRect.y - descent) + (insets.top + ascent + descent) / 2;
            break;
        
        case BELOW_TOP: 
            textLoc.y = grooveRect.y + insets.top + ascent + TEXT_SPACING;
            break;
        
        case ABOVE_BOTTOM: 
            textLoc.y = (grooveRect.y + grooveRect.height) - (insets.bottom + descent + TEXT_SPACING);
            break;
        
        case BOTTOM: 
            grooveRect.height -= fontHeight / 2;
            textLoc.y = ((grooveRect.y + grooveRect.height) - descent) + ((ascent + descent) - insets.bottom) / 2;
            break;
        
        case BELOW_BOTTOM: 
            grooveRect.height -= fontHeight;
            textLoc.y = grooveRect.y + grooveRect.height + ascent + TEXT_SPACING;
            break;
        
        }
        int justification = getTitleJustification();
        if (isLeftToRight(c)) {
            if (justification == LEADING || justification == DEFAULT_JUSTIFICATION) {
                justification = LEFT;
            } else if (justification == TRAILING) {
                justification = RIGHT;
            }
        } else {
            if (justification == LEADING || justification == DEFAULT_JUSTIFICATION) {
                justification = RIGHT;
            } else if (justification == TRAILING) {
                justification = LEFT;
            }
        }
        switch (justification) {
        case LEFT: 
            textLoc.x = grooveRect.x + TEXT_INSET_H + insets.left;
            break;
        
        case RIGHT: 
            textLoc.x = (grooveRect.x + grooveRect.width) - (stringWidth + TEXT_INSET_H + insets.right);
            break;
        
        case CENTER: 
            textLoc.x = grooveRect.x + ((grooveRect.width - stringWidth) / 2);
            break;
        
        }
        if (border != null) {
            if (((titlePos == TOP || titlePos == DEFAULT_POSITION) && (grooveRect.y > textLoc.y - ascent)) || (titlePos == BOTTOM && (grooveRect.y + grooveRect.height < textLoc.y + descent))) {
                Rectangle clipRect = new Rectangle();
                Rectangle saveClip = g.getClipBounds();
                clipRect.setBounds(saveClip);
                if (computeIntersection(clipRect, x, y, textLoc.x - 1 - x, height)) {
                    g.setClip(clipRect);
                    border.paintBorder(c, g, grooveRect.x, grooveRect.y, grooveRect.width, grooveRect.height);
                }
                clipRect.setBounds(saveClip);
                if (computeIntersection(clipRect, textLoc.x + stringWidth + 1, y, x + width - (textLoc.x + stringWidth + 1), height)) {
                    g.setClip(clipRect);
                    border.paintBorder(c, g, grooveRect.x, grooveRect.y, grooveRect.width, grooveRect.height);
                }
                if (titlePos == TOP || titlePos == DEFAULT_POSITION) {
                    clipRect.setBounds(saveClip);
                    if (computeIntersection(clipRect, textLoc.x - 1, textLoc.y + descent, stringWidth + 2, y + height - textLoc.y - descent)) {
                        g.setClip(clipRect);
                        border.paintBorder(c, g, grooveRect.x, grooveRect.y, grooveRect.width, grooveRect.height);
                    }
                } else {
                    clipRect.setBounds(saveClip);
                    if (computeIntersection(clipRect, textLoc.x - 1, y, stringWidth + 2, textLoc.y - ascent - y)) {
                        g.setClip(clipRect);
                        border.paintBorder(c, g, grooveRect.x, grooveRect.y, grooveRect.width, grooveRect.height);
                    }
                }
                g.setClip(saveClip);
            } else {
                border.paintBorder(c, g, grooveRect.x, grooveRect.y, grooveRect.width, grooveRect.height);
            }
        }
        g.setColor(getTitleColor());
        SwingUtilities2.drawString(jc, g, getTitle(), textLoc.x, textLoc.y);
        g.setFont(font);
        g.setColor(color);
    }
    
    public Insets getBorderInsets(Component c) {
        return getBorderInsets(c, new Insets(0, 0, 0, 0));
    }
    
    public Insets getBorderInsets(Component c, Insets insets) {
        FontMetrics fm;
        int descent = 0;
        int ascent = 16;
        int height = 16;
        Border border = getBorder();
        if (border != null) {
            if (border instanceof AbstractBorder) {
                ((AbstractBorder)(AbstractBorder)border).getBorderInsets(c, insets);
            } else {
                Insets i = border.getBorderInsets(c);
                insets.top = i.top;
                insets.right = i.right;
                insets.bottom = i.bottom;
                insets.left = i.left;
            }
        } else {
            insets.left = insets.top = insets.right = insets.bottom = 0;
        }
        insets.left += EDGE_SPACING + TEXT_SPACING;
        insets.right += EDGE_SPACING + TEXT_SPACING;
        insets.top += EDGE_SPACING + TEXT_SPACING;
        insets.bottom += EDGE_SPACING + TEXT_SPACING;
        if (c == null || getTitle() == null || getTitle().equals("")) {
            return insets;
        }
        Font font = getFont(c);
        fm = c.getFontMetrics(font);
        if (fm != null) {
            descent = fm.getDescent();
            ascent = fm.getAscent();
            height = fm.getHeight();
        }
        switch (getTitlePosition()) {
        case ABOVE_TOP: 
            insets.top += ascent + descent + (Math.max(EDGE_SPACING, TEXT_SPACING * 2) - EDGE_SPACING);
            break;
        
        case TOP: 
        
        case DEFAULT_POSITION: 
            insets.top += ascent + descent;
            break;
        
        case BELOW_TOP: 
            insets.top += ascent + descent + TEXT_SPACING;
            break;
        
        case ABOVE_BOTTOM: 
            insets.bottom += ascent + descent + TEXT_SPACING;
            break;
        
        case BOTTOM: 
            insets.bottom += ascent + descent;
            break;
        
        case BELOW_BOTTOM: 
            insets.bottom += height;
            break;
        
        }
        return insets;
    }
    
    public boolean isBorderOpaque() {
        return false;
    }
    
    public String getTitle() {
        return title;
    }
    
    public Border getBorder() {
        Border b = border;
        if (b == null) b = UIManager.getBorder("TitledBorder.border");
        return b;
    }
    
    public int getTitlePosition() {
        return titlePosition;
    }
    
    public int getTitleJustification() {
        return titleJustification;
    }
    
    public Font getTitleFont() {
        Font f = titleFont;
        if (f == null) f = UIManager.getFont("TitledBorder.font");
        return f;
    }
    
    public Color getTitleColor() {
        Color c = titleColor;
        if (c == null) c = UIManager.getColor("TitledBorder.titleColor");
        return c;
    }
    
    public void setTitle(String title) {
        this.title = title;
    }
    
    public void setBorder(Border border) {
        this.border = border;
    }
    
    public void setTitlePosition(int titlePosition) {
        switch (titlePosition) {
        case ABOVE_TOP: 
        
        case TOP: 
        
        case BELOW_TOP: 
        
        case ABOVE_BOTTOM: 
        
        case BOTTOM: 
        
        case BELOW_BOTTOM: 
        
        case DEFAULT_POSITION: 
            this.titlePosition = titlePosition;
            break;
        
        default: 
            throw new IllegalArgumentException(titlePosition + " is not a valid title position.");
        
        }
    }
    
    public void setTitleJustification(int titleJustification) {
        switch (titleJustification) {
        case DEFAULT_JUSTIFICATION: 
        
        case LEFT: 
        
        case CENTER: 
        
        case RIGHT: 
        
        case LEADING: 
        
        case TRAILING: 
            this.titleJustification = titleJustification;
            break;
        
        default: 
            throw new IllegalArgumentException(titleJustification + " is not a valid title justification.");
        
        }
    }
    
    public void setTitleFont(Font titleFont) {
        this.titleFont = titleFont;
    }
    
    public void setTitleColor(Color titleColor) {
        this.titleColor = titleColor;
    }
    
    public Dimension getMinimumSize(Component c) {
        Insets insets = getBorderInsets(c);
        Dimension minSize = new Dimension(insets.right + insets.left, insets.top + insets.bottom);
        Font font = getFont(c);
        FontMetrics fm = c.getFontMetrics(font);
        JComponent jc = (c instanceof JComponent) ? (JComponent)(JComponent)c : null;
        switch (titlePosition) {
        case ABOVE_TOP: 
        
        case BELOW_BOTTOM: 
            minSize.width = Math.max(SwingUtilities2.stringWidth(jc, fm, getTitle()), minSize.width);
            break;
        
        case BELOW_TOP: 
        
        case ABOVE_BOTTOM: 
        
        case TOP: 
        
        case BOTTOM: 
        
        case DEFAULT_POSITION: 
        
        default: 
            minSize.width += SwingUtilities2.stringWidth(jc, fm, getTitle());
        
        }
        return minSize;
    }
    
    protected Font getFont(Component c) {
        Font font;
        if ((font = getTitleFont()) != null) {
            return font;
        } else if (c != null && (font = c.getFont()) != null) {
            return font;
        }
        return new Font("Dialog", Font.PLAIN, 12);
    }
    
    private static boolean computeIntersection(Rectangle dest, int rx, int ry, int rw, int rh) {
        int x1 = Math.max(rx, dest.x);
        int x2 = Math.min(rx + rw, dest.x + dest.width);
        int y1 = Math.max(ry, dest.y);
        int y2 = Math.min(ry + rh, dest.y + dest.height);
        dest.x = x1;
        dest.y = y1;
        dest.width = x2 - x1;
        dest.height = y2 - y1;
        if (dest.width <= 0 || dest.height <= 0) {
            return false;
        }
        return true;
    }
}
