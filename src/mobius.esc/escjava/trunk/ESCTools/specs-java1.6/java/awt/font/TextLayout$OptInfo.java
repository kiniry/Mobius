package java.awt.font;

import java.awt.Font;
import java.awt.Graphics2D;
import java.awt.Shape;
import java.awt.geom.Rectangle2D;
import java.util.Map;
import java.util.HashMap;
import sun.font.AdvanceCache;
import sun.font.CoreMetrics;
import sun.font.Decoration;

class TextLayout$OptInfo implements Decoration$Label {
    private static final float MAGIC_ADVANCE = -12345.67F;
    private FontRenderContext frc;
    private char[] chars;
    private Font font;
    private CoreMetrics metrics;
    private Map attrs;
    private float advance;
    private Rectangle2D vb;
    private Decoration decoration;
    private String str;
    
    private TextLayout$OptInfo(FontRenderContext frc, char[] chars, Font font, CoreMetrics metrics, Map attrs) {
        
        this.frc = frc;
        this.chars = chars;
        this.font = font;
        this.metrics = metrics;
        this.attrs = attrs;
        if (attrs != null) {
            this.attrs = new HashMap(attrs);
        }
        this.advance = MAGIC_ADVANCE;
    }
    
    TextLine createTextLine() {
        return TextLine.fastCreateTextLine(frc, chars, font, metrics, attrs);
    }
    
    float getAdvance() {
        if (advance == MAGIC_ADVANCE) {
            AdvanceCache adv = AdvanceCache.get(font, frc);
            advance = adv.getAdvance(chars, 0, chars.length);
        }
        return advance;
    }
    
    public CoreMetrics getCoreMetrics() {
        return metrics;
    }
    
    public Rectangle2D getLogicalBounds() {
        return new Rectangle2D$Float(0, -metrics.ascent, getAdvance(), metrics.height);
    }
    
    public void handleDraw(Graphics2D g2d, float x, float y) {
        if (str == null) {
            str = new String(chars, 0, chars.length);
        }
        g2d.drawString(str, x, y);
    }
    
    public Rectangle2D handleGetCharVisualBounds(int index) {
        throw new InternalError();
    }
    
    public Rectangle2D handleGetVisualBounds() {
        AdvanceCache adv = AdvanceCache.get(font, frc);
        return adv.getVisualBounds(chars, 0, chars.length);
    }
    
    public Shape handleGetOutline(float x, float y) {
        throw new InternalError();
    }
    
    boolean draw(Graphics2D g2d, float x, float y) {
        if (g2d.getFontRenderContext().equals(frc)) {
            Font oldFont = g2d.getFont();
            g2d.setFont(font);
            getDecoration().drawTextAndDecorations(this, g2d, x, y);
            g2d.setFont(oldFont);
            return true;
        }
        return false;
    }
    
    Rectangle2D getVisualBounds() {
        if (vb == null) {
            vb = getDecoration().getVisualBounds(this);
        }
        return (Rectangle2D)(Rectangle2D)vb.clone();
    }
    
    Decoration getDecoration() {
        if (decoration == null) {
            if (attrs == null) {
                decoration = Decoration.getDecoration(null);
            } else {
                decoration = Decoration.getDecoration(StyledParagraph.addInputMethodAttrs(attrs));
            }
        }
        return decoration;
    }
    
    static TextLayout$OptInfo create(FontRenderContext frc, char[] chars, Font font, CoreMetrics metrics, Map attrs) {
        if (!font.isTransformed() && AdvanceCache.supportsText(chars)) {
            if (attrs == null || attrs.get(TextAttribute.CHAR_REPLACEMENT) == null) {
                return new TextLayout$OptInfo(frc, chars, font, metrics, attrs);
            }
        }
        return null;
    }
}
