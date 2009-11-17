package javax.swing.text;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;

class DefaultHighlighter$HighlightInfo implements Highlighter$Highlight {
    /*synthetic*/ final DefaultHighlighter this$0;
    
    DefaultHighlighter$HighlightInfo(/*synthetic*/ final DefaultHighlighter this$0) {
        this.this$0 = this$0;
        
    }
    
    public int getStartOffset() {
        return p0.getOffset();
    }
    
    public int getEndOffset() {
        return p1.getOffset();
    }
    
    public Highlighter$HighlightPainter getPainter() {
        return painter;
    }
    Position p0;
    Position p1;
    Highlighter$HighlightPainter painter;
}
