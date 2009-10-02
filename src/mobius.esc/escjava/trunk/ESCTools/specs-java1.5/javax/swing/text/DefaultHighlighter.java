package javax.swing.text;

import java.util.Vector;
import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;

public class DefaultHighlighter extends LayeredHighlighter {
    
    /*synthetic*/ static JTextComponent access$000(DefaultHighlighter x0) {
        return x0.component;
    }
    
    public DefaultHighlighter() {
        
        drawsLayeredHighlights = true;
    }
    
    public void paint(Graphics g) {
        int len = highlights.size();
        for (int i = 0; i < len; i++) {
            DefaultHighlighter$HighlightInfo info = (DefaultHighlighter$HighlightInfo)(DefaultHighlighter$HighlightInfo)highlights.elementAt(i);
            if (!(info instanceof DefaultHighlighter$LayeredHighlightInfo)) {
                Rectangle a = component.getBounds();
                Insets insets = component.getInsets();
                a.x = insets.left;
                a.y = insets.top;
                a.width -= insets.left + insets.right;
                a.height -= insets.top + insets.bottom;
                for (; i < len; i++) {
                    info = (DefaultHighlighter$HighlightInfo)(DefaultHighlighter$HighlightInfo)highlights.elementAt(i);
                    if (!(info instanceof DefaultHighlighter$LayeredHighlightInfo)) {
                        Highlighter$HighlightPainter p = info.getPainter();
                        p.paint(g, info.getStartOffset(), info.getEndOffset(), a, component);
                    }
                }
            }
        }
    }
    
    public void install(JTextComponent c) {
        component = c;
        removeAllHighlights();
    }
    
    public void deinstall(JTextComponent c) {
        component = null;
    }
    
    public Object addHighlight(int p0, int p1, Highlighter$HighlightPainter p) throws BadLocationException {
        Document doc = component.getDocument();
        DefaultHighlighter$HighlightInfo i = (getDrawsLayeredHighlights() && (p instanceof LayeredHighlighter$LayerPainter)) ? new DefaultHighlighter$LayeredHighlightInfo(this) : new DefaultHighlighter$HighlightInfo(this);
        i.painter = p;
        i.p0 = doc.createPosition(p0);
        i.p1 = doc.createPosition(p1);
        highlights.addElement(i);
        safeDamageRange(p0, p1);
        return i;
    }
    
    public void removeHighlight(Object tag) {
        if (tag instanceof DefaultHighlighter$LayeredHighlightInfo) {
            DefaultHighlighter$LayeredHighlightInfo lhi = (DefaultHighlighter$LayeredHighlightInfo)(DefaultHighlighter$LayeredHighlightInfo)tag;
            if (lhi.width > 0 && lhi.height > 0) {
                component.repaint(lhi.x, lhi.y, lhi.width, lhi.height);
            }
        } else {
            DefaultHighlighter$HighlightInfo info = (DefaultHighlighter$HighlightInfo)(DefaultHighlighter$HighlightInfo)tag;
            safeDamageRange(info.p0, info.p1);
        }
        highlights.removeElement(tag);
    }
    
    public void removeAllHighlights() {
        TextUI mapper = component.getUI();
        if (getDrawsLayeredHighlights()) {
            int len = highlights.size();
            if (len != 0) {
                int minX = 0;
                int minY = 0;
                int maxX = 0;
                int maxY = 0;
                int p0 = -1;
                int p1 = -1;
                for (int i = 0; i < len; i++) {
                    DefaultHighlighter$HighlightInfo hi = (DefaultHighlighter$HighlightInfo)(DefaultHighlighter$HighlightInfo)highlights.elementAt(i);
                    if (hi instanceof DefaultHighlighter$LayeredHighlightInfo) {
                        DefaultHighlighter$LayeredHighlightInfo info = (DefaultHighlighter$LayeredHighlightInfo)(DefaultHighlighter$LayeredHighlightInfo)hi;
                        minX = Math.min(minX, info.x);
                        minY = Math.min(minY, info.y);
                        maxX = Math.max(maxX, info.x + info.width);
                        maxY = Math.max(maxY, info.y + info.height);
                    } else {
                        if (p0 == -1) {
                            p0 = hi.p0.getOffset();
                            p1 = hi.p1.getOffset();
                        } else {
                            p0 = Math.min(p0, hi.p0.getOffset());
                            p1 = Math.max(p1, hi.p1.getOffset());
                        }
                    }
                }
                if (minX != maxX && minY != maxY) {
                    component.repaint(minX, minY, maxX - minX, maxY - minY);
                }
                if (p0 != -1) {
                    try {
                        safeDamageRange(p0, p1);
                    } catch (BadLocationException e) {
                    }
                }
                highlights.removeAllElements();
            }
        } else if (mapper != null) {
            int len = highlights.size();
            if (len != 0) {
                int p0 = Integer.MAX_VALUE;
                int p1 = 0;
                for (int i = 0; i < len; i++) {
                    DefaultHighlighter$HighlightInfo info = (DefaultHighlighter$HighlightInfo)(DefaultHighlighter$HighlightInfo)highlights.elementAt(i);
                    p0 = Math.min(p0, info.p0.getOffset());
                    p1 = Math.max(p1, info.p1.getOffset());
                }
                try {
                    safeDamageRange(p0, p1);
                } catch (BadLocationException e) {
                }
                highlights.removeAllElements();
            }
        }
    }
    
    public void changeHighlight(Object tag, int p0, int p1) throws BadLocationException {
        Document doc = component.getDocument();
        if (tag instanceof DefaultHighlighter$LayeredHighlightInfo) {
            DefaultHighlighter$LayeredHighlightInfo lhi = (DefaultHighlighter$LayeredHighlightInfo)(DefaultHighlighter$LayeredHighlightInfo)tag;
            if (lhi.width > 0 && lhi.height > 0) {
                component.repaint(lhi.x, lhi.y, lhi.width, lhi.height);
            }
            lhi.width = lhi.height = 0;
            lhi.p0 = doc.createPosition(p0);
            lhi.p1 = doc.createPosition(p1);
            safeDamageRange(Math.min(p0, p1), Math.max(p0, p1));
        } else {
            DefaultHighlighter$HighlightInfo info = (DefaultHighlighter$HighlightInfo)(DefaultHighlighter$HighlightInfo)tag;
            int oldP0 = info.p0.getOffset();
            int oldP1 = info.p1.getOffset();
            if (p0 == oldP0) {
                safeDamageRange(Math.min(oldP1, p1), Math.max(oldP1, p1));
            } else if (p1 == oldP1) {
                safeDamageRange(Math.min(p0, oldP0), Math.max(p0, oldP0));
            } else {
                safeDamageRange(oldP0, oldP1);
                safeDamageRange(p0, p1);
            }
            info.p0 = doc.createPosition(p0);
            info.p1 = doc.createPosition(p1);
        }
    }
    
    public Highlighter$Highlight[] getHighlights() {
        int size = highlights.size();
        if (size == 0) {
            return noHighlights;
        }
        Highlighter$Highlight[] h = new Highlighter$Highlight[size];
        highlights.copyInto(h);
        return h;
    }
    
    public void paintLayeredHighlights(Graphics g, int p0, int p1, Shape viewBounds, JTextComponent editor, View view) {
        for (int counter = highlights.size() - 1; counter >= 0; counter--) {
            Object tag = highlights.elementAt(counter);
            if (tag instanceof DefaultHighlighter$LayeredHighlightInfo) {
                DefaultHighlighter$LayeredHighlightInfo lhi = (DefaultHighlighter$LayeredHighlightInfo)(DefaultHighlighter$LayeredHighlightInfo)tag;
                int start = lhi.getStartOffset();
                int end = lhi.getEndOffset();
                if ((p0 < start && p1 > start) || (p0 >= start && p0 < end)) {
                    lhi.paintLayeredHighlights(g, p0, p1, viewBounds, editor, view);
                }
            }
        }
    }
    
    private void safeDamageRange(final Position p0, final Position p1) {
        safeDamager.damageRange(p0, p1);
    }
    
    private void safeDamageRange(int a0, int a1) throws BadLocationException {
        Document doc = component.getDocument();
        safeDamageRange(doc.createPosition(a0), doc.createPosition(a1));
    }
    
    public void setDrawsLayeredHighlights(boolean newValue) {
        drawsLayeredHighlights = newValue;
    }
    
    public boolean getDrawsLayeredHighlights() {
        return drawsLayeredHighlights;
    }
    private static final Highlighter$Highlight[] noHighlights = new Highlighter$Highlight[0];
    private Vector highlights = new Vector();
    private JTextComponent component;
    private boolean drawsLayeredHighlights;
    private DefaultHighlighter$SafeDamager safeDamager = new DefaultHighlighter$SafeDamager(this);
    public static final LayeredHighlighter$LayerPainter DefaultPainter = new DefaultHighlighter$DefaultHighlightPainter(null);
    {
    }
    {
    }
    {
    }
    {
    }
}
