package javax.swing.text;

import java.util.Vector;
import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;

class DefaultHighlighter$SafeDamager implements Runnable {
    /*synthetic*/ final DefaultHighlighter this$0;
    
    DefaultHighlighter$SafeDamager(/*synthetic*/ final DefaultHighlighter this$0) {
        this.this$0 = this$0;
        
    }
    private Vector p0 = new Vector(10);
    private Vector p1 = new Vector(10);
    private Document lastDoc = null;
    
    public synchronized void run() {
        if (DefaultHighlighter.access$000(this$0) != null) {
            TextUI mapper = DefaultHighlighter.access$000(this$0).getUI();
            if (mapper != null && lastDoc == DefaultHighlighter.access$000(this$0).getDocument()) {
                int len = p0.size();
                for (int i = 0; i < len; i++) {
                    mapper.damageRange(DefaultHighlighter.access$000(this$0), ((Position)(Position)p0.get(i)).getOffset(), ((Position)(Position)p1.get(i)).getOffset());
                }
            }
        }
        p0.clear();
        p1.clear();
        lastDoc = null;
    }
    
    public synchronized void damageRange(Position pos0, Position pos1) {
        if (DefaultHighlighter.access$000(this$0) == null) {
            p0.clear();
            lastDoc = null;
            return;
        }
        boolean addToQueue = p0.isEmpty();
        Document curDoc = DefaultHighlighter.access$000(this$0).getDocument();
        if (curDoc != lastDoc) {
            if (!p0.isEmpty()) {
                p0.clear();
                p1.clear();
            }
            lastDoc = curDoc;
        }
        p0.add(pos0);
        p1.add(pos1);
        if (addToQueue) {
            SwingUtilities.invokeLater(this);
        }
    }
}
