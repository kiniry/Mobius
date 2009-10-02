package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.net.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.event.*;

class ImageView$ImageLabelView extends InlineView {
    /*synthetic*/ final ImageView this$0;
    private Segment segment;
    private Color fg;
    
    ImageView$ImageLabelView(/*synthetic*/ final ImageView this$0, Element e, String text) {
        this.this$0 = this$0;
        super(e);
        reset(text);
    }
    
    public void reset(String text) {
        segment = new Segment(text.toCharArray(), 0, text.length());
    }
    
    public void paint(Graphics g, Shape a) {
        GlyphView$GlyphPainter painter = getGlyphPainter();
        if (painter != null) {
            g.setColor(getForeground());
            painter.paint(this, g, a, getStartOffset(), getEndOffset());
        }
    }
    
    public Segment getText(int p0, int p1) {
        if (p0 < 0 || p1 > segment.array.length) {
            throw new RuntimeException("ImageLabelView: Stale view");
        }
        segment.offset = p0;
        segment.count = p1 - p0;
        return segment;
    }
    
    public int getStartOffset() {
        return 0;
    }
    
    public int getEndOffset() {
        return segment.array.length;
    }
    
    public View breakView(int axis, int p0, float pos, float len) {
        return this;
    }
    
    public Color getForeground() {
        View parent;
        if (fg == null && (parent = getParent()) != null) {
            Document doc = getDocument();
            AttributeSet attr = parent.getAttributes();
            if (attr != null && (doc instanceof StyledDocument)) {
                fg = ((StyledDocument)(StyledDocument)doc).getForeground(attr);
            }
        }
        return fg;
    }
}
