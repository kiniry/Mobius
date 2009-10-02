package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;
import javax.accessibility.*;
import java.lang.ref.*;

class HTMLEditorKit$NavigateLinkAction$FocusHighlightPainter extends DefaultHighlighter$DefaultHighlightPainter {
    /*synthetic*/ final HTMLEditorKit$NavigateLinkAction this$0;
    
    HTMLEditorKit$NavigateLinkAction$FocusHighlightPainter(/*synthetic*/ final HTMLEditorKit$NavigateLinkAction this$0, Color color) {
        this.this$0 = this$0;
        super(color);
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
            g.drawRect(alloc.x, alloc.y, alloc.width - 1, alloc.height);
            return alloc;
        } else {
            try {
                Shape shape = view.modelToView(offs0, Position$Bias.Forward, offs1, Position$Bias.Backward, bounds);
                Rectangle r = (shape instanceof Rectangle) ? (Rectangle)(Rectangle)shape : shape.getBounds();
                g.drawRect(r.x, r.y, r.width - 1, r.height);
                return r;
            } catch (BadLocationException e) {
            }
        }
        return null;
    }
}
