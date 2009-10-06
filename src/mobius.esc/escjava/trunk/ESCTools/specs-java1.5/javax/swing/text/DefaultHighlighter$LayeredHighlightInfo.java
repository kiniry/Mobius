package javax.swing.text;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;

class DefaultHighlighter$LayeredHighlightInfo extends DefaultHighlighter$HighlightInfo {
    /*synthetic*/ final DefaultHighlighter this$0;
    
    DefaultHighlighter$LayeredHighlightInfo(/*synthetic*/ final DefaultHighlighter this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    void union(Shape bounds) {
        if (bounds == null) return;
        Rectangle alloc;
        if (bounds instanceof Rectangle) {
            alloc = (Rectangle)(Rectangle)bounds;
        } else {
            alloc = bounds.getBounds();
        }
        if (width == 0 || height == 0) {
            x = alloc.x;
            y = alloc.y;
            width = alloc.width;
            height = alloc.height;
        } else {
            width = Math.max(x + width, alloc.x + alloc.width);
            height = Math.max(y + height, alloc.y + alloc.height);
            x = Math.min(x, alloc.x);
            width -= x;
            y = Math.min(y, alloc.y);
            height -= y;
        }
    }
    
    void paintLayeredHighlights(Graphics g, int p0, int p1, Shape viewBounds, JTextComponent editor, View view) {
        int start = getStartOffset();
        int end = getEndOffset();
        p0 = Math.max(start, p0);
        p1 = Math.min(end, p1);
        union(((LayeredHighlighter$LayerPainter)(LayeredHighlighter$LayerPainter)painter).paintLayer(g, p0, p1, viewBounds, editor, view));
    }
    int x;
    int y;
    int width;
    int height;
}
