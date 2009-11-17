package javax.swing.text;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;

public class DefaultHighlighter$DefaultHighlightPainter extends LayeredHighlighter$LayerPainter {
    
    public DefaultHighlighter$DefaultHighlightPainter(Color c) {
        
        color = c;
    }
    
    public Color getColor() {
        return color;
    }
    
    public void paint(Graphics g, int offs0, int offs1, Shape bounds, JTextComponent c) {
        Rectangle alloc = bounds.getBounds();
        try {
            TextUI mapper = c.getUI();
            Rectangle p0 = mapper.modelToView(c, offs0);
            Rectangle p1 = mapper.modelToView(c, offs1);
            Color color = getColor();
            if (color == null) {
                g.setColor(c.getSelectionColor());
            } else {
                g.setColor(color);
            }
            if (p0.y == p1.y) {
                Rectangle r = p0.union(p1);
                g.fillRect(r.x, r.y, r.width, r.height);
            } else {
                int p0ToMarginWidth = alloc.x + alloc.width - p0.x;
                g.fillRect(p0.x, p0.y, p0ToMarginWidth, p0.height);
                if ((p0.y + p0.height) != p1.y) {
                    g.fillRect(alloc.x, p0.y + p0.height, alloc.width, p1.y - (p0.y + p0.height));
                }
                g.fillRect(alloc.x, p1.y, (p1.x - alloc.x), p1.height);
            }
        } catch (BadLocationException e) {
        }
    }
    
    public Shape paintLayer(Graphics g, int offs0, int offs1, Shape bounds, JTextComponent c, View view) {
        Color color = getColor();
        if (color == null) {
            g.setColor(c.getSelectionColor());
        } else {
            g.setColor(color);
        }
        if (offs0 == view.getStartOffset() && offs1 == view.getEndOffset()) {
            Rectangle alloc;
            if (bounds instanceof Rectangle) {
                alloc = (Rectangle)(Rectangle)bounds;
            } else {
                alloc = bounds.getBounds();
            }
            g.fillRect(alloc.x, alloc.y, alloc.width, alloc.height);
            return alloc;
        } else {
            try {
                Shape shape = view.modelToView(offs0, Position$Bias.Forward, offs1, Position$Bias.Backward, bounds);
                Rectangle r = (shape instanceof Rectangle) ? (Rectangle)(Rectangle)shape : shape.getBounds();
                g.fillRect(r.x, r.y, r.width, r.height);
                return r;
            } catch (BadLocationException e) {
            }
        }
        return null;
    }
    private Color color;
}
