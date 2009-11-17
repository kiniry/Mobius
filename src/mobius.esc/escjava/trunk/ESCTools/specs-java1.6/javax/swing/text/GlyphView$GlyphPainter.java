package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

public abstract class GlyphView$GlyphPainter {
    
    public GlyphView$GlyphPainter() {
        
    }
    
    public abstract float getSpan(GlyphView v, int p0, int p1, TabExpander e, float x);
    
    public abstract float getHeight(GlyphView v);
    
    public abstract float getAscent(GlyphView v);
    
    public abstract float getDescent(GlyphView v);
    
    public abstract void paint(GlyphView v, Graphics g, Shape a, int p0, int p1);
    
    public abstract Shape modelToView(GlyphView v, int pos, Position$Bias bias, Shape a) throws BadLocationException;
    
    public abstract int viewToModel(GlyphView v, float x, float y, Shape a, Position$Bias[] biasReturn);
    
    public abstract int getBoundedPosition(GlyphView v, int p0, float x, float len);
    
    public GlyphView$GlyphPainter getPainter(GlyphView v, int p0, int p1) {
        return this;
    }
    
    public int getNextVisualPositionFrom(GlyphView v, int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet) throws BadLocationException {
        int startOffset = v.getStartOffset();
        int endOffset = v.getEndOffset();
        Segment text;
        switch (direction) {
        case View.NORTH: 
        
        case View.SOUTH: 
            if (pos != -1) {
                return -1;
            }
            Container container = v.getContainer();
            if (container instanceof JTextComponent) {
                Caret c = ((JTextComponent)(JTextComponent)container).getCaret();
                Point magicPoint;
                magicPoint = (c != null) ? c.getMagicCaretPosition() : null;
                if (magicPoint == null) {
                    biasRet[0] = Position$Bias.Forward;
                    return startOffset;
                }
                int value = v.viewToModel(magicPoint.x, 0.0F, a, biasRet);
                return value;
            }
            break;
        
        case View.EAST: 
            if (startOffset == v.getDocument().getLength()) {
                if (pos == -1) {
                    biasRet[0] = Position$Bias.Forward;
                    return startOffset;
                }
                return -1;
            }
            if (pos == -1) {
                biasRet[0] = Position$Bias.Forward;
                return startOffset;
            }
            if (pos == endOffset) {
                return -1;
            }
            if (++pos == endOffset) {
                return -1;
            } else {
                biasRet[0] = Position$Bias.Forward;
            }
            return pos;
        
        case View.WEST: 
            if (startOffset == v.getDocument().getLength()) {
                if (pos == -1) {
                    biasRet[0] = Position$Bias.Forward;
                    return startOffset;
                }
                return -1;
            }
            if (pos == -1) {
                biasRet[0] = Position$Bias.Forward;
                return endOffset - 1;
            }
            if (pos == startOffset) {
                return -1;
            }
            biasRet[0] = Position$Bias.Forward;
            return (pos - 1);
        
        default: 
            throw new IllegalArgumentException("Bad direction: " + direction);
        
        }
        return pos;
    }
}
