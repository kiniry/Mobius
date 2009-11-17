package javax.swing.text;

import java.awt.Graphics;
import java.awt.Shape;

public abstract class LayeredHighlighter implements Highlighter {
    
    public LayeredHighlighter() {
        
    }
    
    public abstract void paintLayeredHighlights(Graphics g, int p0, int p1, Shape viewBounds, JTextComponent editor, View view);
    {
    }
}
