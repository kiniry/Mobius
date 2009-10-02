package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JTextComponent$ComposedTextCaret extends DefaultCaret implements Serializable {
    /*synthetic*/ final JTextComponent this$0;
    
    JTextComponent$ComposedTextCaret(/*synthetic*/ final JTextComponent this$0) {
        this.this$0 = this$0;
        
    }
    Color bg;
    
    public void install(JTextComponent c) {
        super.install(c);
        Document doc = c.getDocument();
        if (doc instanceof StyledDocument) {
            StyledDocument sDoc = (StyledDocument)(StyledDocument)doc;
            Element elem = sDoc.getCharacterElement(JTextComponent.access$800(c).getOffset());
            AttributeSet attr = elem.getAttributes();
            bg = sDoc.getBackground(attr);
        }
        if (bg == null) {
            bg = c.getBackground();
        }
    }
    
    public void paint(Graphics g) {
        if (isVisible()) {
            try {
                Rectangle r = component.modelToView(getDot());
                g.setXORMode(bg);
                g.drawLine(r.x, r.y, r.x, r.y + r.height - 1);
                g.setPaintMode();
            } catch (BadLocationException e) {
            }
        }
    }
    
    protected void positionCaret(MouseEvent me) {
        JTextComponent host = component;
        Point pt = new Point(me.getX(), me.getY());
        int offset = host.viewToModel(pt);
        int composedStartIndex = JTextComponent.access$800(host).getOffset();
        if ((offset < composedStartIndex) || (offset > JTextComponent.access$900(this$0).getOffset())) {
            try {
                Position newPos = host.getDocument().createPosition(offset);
                host.getInputContext().endComposition();
                EventQueue.invokeLater(new JTextComponent$DoSetCaretPosition(this$0, host, newPos));
            } catch (BadLocationException ble) {
                System.err.println(ble);
            }
        } else {
            super.positionCaret(me);
        }
    }
}
