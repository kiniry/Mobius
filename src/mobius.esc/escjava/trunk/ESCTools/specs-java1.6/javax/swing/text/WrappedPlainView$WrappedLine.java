package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

class WrappedPlainView$WrappedLine extends View {
    /*synthetic*/ final WrappedPlainView this$0;
    
    WrappedPlainView$WrappedLine(/*synthetic*/ final WrappedPlainView this$0, Element elem) {
        super(elem);
        this.this$0 = this$0;
    }
    
    final int calculateLineCount() {
        int nlines = 0;
        int p1 = getEndOffset();
        for (int p0 = getStartOffset(); p0 < p1; ) {
            nlines += 1;
            int p = this$0.calculateBreakPosition(p0, p1);
            p0 = (p == p0) ? ++p : p;
        }
        return nlines;
    }
    
    public float getPreferredSpan(int axis) {
        switch (axis) {
        case View.X_AXIS: 
            float width = this$0.getWidth();
            if (width == Integer.MAX_VALUE) {
                return 100.0F;
            }
            return width;
        
        case View.Y_AXIS: 
            if (nlines == 0 || this$0.widthChanging) {
                nlines = calculateLineCount();
            }
            int h = nlines * this$0.metrics.getHeight();
            return h;
        
        default: 
            throw new IllegalArgumentException("Invalid axis: " + axis);
        
        }
    }
    
    public void paint(Graphics g, Shape a) {
        Rectangle alloc = (Rectangle)(Rectangle)a;
        int y = alloc.y + this$0.metrics.getAscent();
        int x = alloc.x;
        JTextComponent host = (JTextComponent)(JTextComponent)getContainer();
        Highlighter h = host.getHighlighter();
        LayeredHighlighter dh = (h instanceof LayeredHighlighter) ? (LayeredHighlighter)(LayeredHighlighter)h : null;
        int p1 = getEndOffset();
        for (int p0 = getStartOffset(); p0 < p1; ) {
            int p = this$0.calculateBreakPosition(p0, p1);
            if (dh != null) {
                if (p == p1) {
                    dh.paintLayeredHighlights(g, p0, p - 1, a, host, this);
                } else {
                    dh.paintLayeredHighlights(g, p0, p, a, host, this);
                }
            }
            this$0.drawLine(p0, p, g, x, y);
            p0 = (p == p0) ? p1 : p;
            y += this$0.metrics.getHeight();
        }
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        Rectangle alloc = a.getBounds();
        alloc.height = this$0.metrics.getHeight();
        alloc.width = 1;
        int p1 = getEndOffset();
        int p0 = getStartOffset();
        int testP = (b == Position$Bias.Forward) ? pos : Math.max(p0, pos - 1);
        while (p0 < p1) {
            int p = this$0.calculateBreakPosition(p0, p1);
            if ((pos >= p0) && (testP < p)) {
                Segment segment = SegmentCache.getSharedSegment();
                this$0.loadText(segment, p0, pos);
                alloc.x += Utilities.getTabbedTextWidth(segment, this$0.metrics, alloc.x, this$0, p0);
                SegmentCache.releaseSharedSegment(segment);
                return alloc;
            }
            if (p == p1 && pos == p1) {
                if (pos > p0) {
                    Segment segment = SegmentCache.getSharedSegment();
                    this$0.loadText(segment, p0, pos);
                    alloc.x += Utilities.getTabbedTextWidth(segment, this$0.metrics, alloc.x, this$0, p0);
                    SegmentCache.releaseSharedSegment(segment);
                }
                return alloc;
            }
            p0 = (p == p0) ? p1 : p;
            alloc.y += alloc.height;
        }
        throw new BadLocationException(null, pos);
    }
    
    public int viewToModel(float fx, float fy, Shape a, Position$Bias[] bias) {
        bias[0] = Position$Bias.Forward;
        Rectangle alloc = (Rectangle)(Rectangle)a;
        Document doc = getDocument();
        int x = (int)fx;
        int y = (int)fy;
        if (y < alloc.y) {
            return getStartOffset();
        } else if (y > alloc.y + alloc.height) {
            return getEndOffset() - 1;
        } else {
            alloc.height = this$0.metrics.getHeight();
            int p1 = getEndOffset();
            for (int p0 = getStartOffset(); p0 < p1; ) {
                int p = this$0.calculateBreakPosition(p0, p1);
                if ((y >= alloc.y) && (y < (alloc.y + alloc.height))) {
                    if (x < alloc.x) {
                        return p0;
                    } else if (x > alloc.x + alloc.width) {
                        return p - 1;
                    } else {
                        Segment segment = SegmentCache.getSharedSegment();
                        this$0.loadText(segment, p0, p1);
                        int n = Utilities.getTabbedTextOffset(segment, this$0.metrics, alloc.x, x, this$0, p0);
                        SegmentCache.releaseSharedSegment(segment);
                        return Math.min(p0 + n, p1 - 1);
                    }
                }
                p0 = (p == p0) ? p1 : p;
                alloc.y += alloc.height;
            }
            return getEndOffset() - 1;
        }
    }
    
    public void insertUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        int n = calculateLineCount();
        if (this.nlines != n) {
            this.nlines = n;
            this$0.preferenceChanged(this, false, true);
            getContainer().repaint();
        } else if (a != null) {
            Component c = getContainer();
            Rectangle alloc = (Rectangle)(Rectangle)a;
            c.repaint(alloc.x, alloc.y, alloc.width, alloc.height);
        }
    }
    
    public void removeUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        int n = calculateLineCount();
        if (this.nlines != n) {
            this.nlines = n;
            this$0.preferenceChanged(this, false, true);
            getContainer().repaint();
        } else if (a != null) {
            Component c = getContainer();
            Rectangle alloc = (Rectangle)(Rectangle)a;
            c.repaint(alloc.x, alloc.y, alloc.width, alloc.height);
        }
    }
    int nlines;
}
