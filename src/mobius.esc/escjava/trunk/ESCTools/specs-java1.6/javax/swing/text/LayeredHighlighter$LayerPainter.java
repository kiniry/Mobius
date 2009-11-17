package javax.swing.text;

import java.awt.Graphics;
import java.awt.Shape;

public abstract class LayeredHighlighter$LayerPainter implements Highlighter$HighlightPainter {
    
    public LayeredHighlighter$LayerPainter() {
        
    }
    
    public abstract Shape paintLayer(Graphics g, int p0, int p1, Shape viewBounds, JTextComponent editor, View view);
}
