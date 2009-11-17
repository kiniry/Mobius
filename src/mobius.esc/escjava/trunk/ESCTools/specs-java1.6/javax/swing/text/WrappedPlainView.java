package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

public class WrappedPlainView extends BoxView implements TabExpander {
    
    public WrappedPlainView(Element elem) {
        this(elem, false);
    }
    
    public WrappedPlainView(Element elem, boolean wordWrap) {
        super(elem, Y_AXIS);
        this.wordWrap = wordWrap;
    }
    
    protected int getTabSize() {
        Integer i = (Integer)(Integer)getDocument().getProperty(PlainDocument.tabSizeAttribute);
        int size = (i != null) ? i.intValue() : 8;
        return size;
    }
    
    protected void drawLine(int p0, int p1, Graphics g, int x, int y) {
        Element lineMap = getElement();
        Element line = lineMap.getElement(lineMap.getElementIndex(p0));
        Element elem;
        try {
            if (line.isLeaf()) {
                drawText(line, p0, p1, g, x, y);
            } else {
                int idx = line.getElementIndex(p0);
                int lastIdx = line.getElementIndex(p1);
                for (; idx <= lastIdx; idx++) {
                    elem = line.getElement(idx);
                    int start = Math.max(elem.getStartOffset(), p0);
                    int end = Math.min(elem.getEndOffset(), p1);
                    x = drawText(elem, start, end, g, x, y);
                }
            }
        } catch (BadLocationException e) {
            throw new StateInvariantError("Can\'t render: " + p0 + "," + p1);
        }
    }
    
    private int drawText(Element elem, int p0, int p1, Graphics g, int x, int y) throws BadLocationException {
        p1 = Math.min(getDocument().getLength(), p1);
        AttributeSet attr = elem.getAttributes();
        if (Utilities.isComposedTextAttributeDefined(attr)) {
            g.setColor(unselected);
            x = Utilities.drawComposedText(this, attr, g, x, y, p0 - elem.getStartOffset(), p1 - elem.getStartOffset());
        } else {
            if (sel0 == sel1 || selected == unselected) {
                x = drawUnselectedText(g, x, y, p0, p1);
            } else if ((p0 >= sel0 && p0 <= sel1) && (p1 >= sel0 && p1 <= sel1)) {
                x = drawSelectedText(g, x, y, p0, p1);
            } else if (sel0 >= p0 && sel0 <= p1) {
                if (sel1 >= p0 && sel1 <= p1) {
                    x = drawUnselectedText(g, x, y, p0, sel0);
                    x = drawSelectedText(g, x, y, sel0, sel1);
                    x = drawUnselectedText(g, x, y, sel1, p1);
                } else {
                    x = drawUnselectedText(g, x, y, p0, sel0);
                    x = drawSelectedText(g, x, y, sel0, p1);
                }
            } else if (sel1 >= p0 && sel1 <= p1) {
                x = drawSelectedText(g, x, y, p0, sel1);
                x = drawUnselectedText(g, x, y, sel1, p1);
            } else {
                x = drawUnselectedText(g, x, y, p0, p1);
            }
        }
        return x;
    }
    
    protected int drawUnselectedText(Graphics g, int x, int y, int p0, int p1) throws BadLocationException {
        g.setColor(unselected);
        Document doc = getDocument();
        Segment segment = SegmentCache.getSharedSegment();
        doc.getText(p0, p1 - p0, segment);
        int ret = Utilities.drawTabbedText(this, segment, x, y, g, this, p0);
        SegmentCache.releaseSharedSegment(segment);
        return ret;
    }
    
    protected int drawSelectedText(Graphics g, int x, int y, int p0, int p1) throws BadLocationException {
        g.setColor(selected);
        Document doc = getDocument();
        Segment segment = SegmentCache.getSharedSegment();
        doc.getText(p0, p1 - p0, segment);
        int ret = Utilities.drawTabbedText(this, segment, x, y, g, this, p0);
        SegmentCache.releaseSharedSegment(segment);
        return ret;
    }
    
    protected final Segment getLineBuffer() {
        if (lineBuffer == null) {
            lineBuffer = new Segment();
        }
        return lineBuffer;
    }
    
    protected int calculateBreakPosition(int p0, int p1) {
        int p;
        Segment segment = SegmentCache.getSharedSegment();
        loadText(segment, p0, p1);
        int currentWidth = getWidth();
        if (wordWrap) {
            p = p0 + Utilities.getBreakLocation(segment, metrics, tabBase, tabBase + currentWidth, this, p0);
        } else {
            p = p0 + Utilities.getTabbedTextOffset(segment, metrics, tabBase, tabBase + currentWidth, this, p0, false);
        }
        SegmentCache.releaseSharedSegment(segment);
        return p;
    }
    
    protected void loadChildren(ViewFactory f) {
        Element e = getElement();
        int n = e.getElementCount();
        if (n > 0) {
            View[] added = new View[n];
            for (int i = 0; i < n; i++) {
                added[i] = new WrappedPlainView$WrappedLine(this, e.getElement(i));
            }
            replace(0, 0, added);
        }
    }
    
    void updateChildren(DocumentEvent e, Shape a) {
        Element elem = getElement();
        DocumentEvent$ElementChange ec = e.getChange(elem);
        if (ec != null) {
            Element[] removedElems = ec.getChildrenRemoved();
            Element[] addedElems = ec.getChildrenAdded();
            View[] added = new View[addedElems.length];
            for (int i = 0; i < addedElems.length; i++) {
                added[i] = new WrappedPlainView$WrappedLine(this, addedElems[i]);
            }
            replace(ec.getIndex(), removedElems.length, added);
            if (a != null) {
                preferenceChanged(null, true, true);
                getContainer().repaint();
            }
        }
        updateMetrics();
    }
    
    final void loadText(Segment segment, int p0, int p1) {
        try {
            Document doc = getDocument();
            doc.getText(p0, p1 - p0, segment);
        } catch (BadLocationException bl) {
            throw new StateInvariantError("Can\'t get line text");
        }
    }
    
    final void updateMetrics() {
        Component host = getContainer();
        Font f = host.getFont();
        metrics = host.getFontMetrics(f);
        tabSize = getTabSize() * metrics.charWidth('m');
    }
    
    public float nextTabStop(float x, int tabOffset) {
        if (tabSize == 0) return x;
        int ntabs = ((int)x - tabBase) / tabSize;
        return tabBase + ((ntabs + 1) * tabSize);
    }
    
    public void paint(Graphics g, Shape a) {
        Rectangle alloc = (Rectangle)(Rectangle)a;
        tabBase = alloc.x;
        JTextComponent host = (JTextComponent)(JTextComponent)getContainer();
        sel0 = host.getSelectionStart();
        sel1 = host.getSelectionEnd();
        unselected = (host.isEnabled()) ? host.getForeground() : host.getDisabledTextColor();
        Caret c = host.getCaret();
        selected = c.isSelectionVisible() && host.getHighlighter() != null ? host.getSelectedTextColor() : unselected;
        g.setFont(host.getFont());
        super.paint(g, a);
    }
    
    public void setSize(float width, float height) {
        updateMetrics();
        if ((int)width != getWidth()) {
            preferenceChanged(null, true, true);
            widthChanging = true;
        }
        super.setSize(width, height);
        widthChanging = false;
    }
    
    public float getPreferredSpan(int axis) {
        updateMetrics();
        return super.getPreferredSpan(axis);
    }
    
    public float getMinimumSpan(int axis) {
        updateMetrics();
        return super.getMinimumSpan(axis);
    }
    
    public float getMaximumSpan(int axis) {
        updateMetrics();
        return super.getMaximumSpan(axis);
    }
    
    public void insertUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        updateChildren(e, a);
        Rectangle alloc = ((a != null) && isAllocationValid()) ? getInsideAllocation(a) : null;
        int pos = e.getOffset();
        View v = getViewAtPosition(pos, alloc);
        if (v != null) {
            v.insertUpdate(e, alloc, f);
        }
    }
    
    public void removeUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        updateChildren(e, a);
        Rectangle alloc = ((a != null) && isAllocationValid()) ? getInsideAllocation(a) : null;
        int pos = e.getOffset();
        View v = getViewAtPosition(pos, alloc);
        if (v != null) {
            v.removeUpdate(e, alloc, f);
        }
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        updateChildren(e, a);
    }
    FontMetrics metrics;
    Segment lineBuffer;
    boolean widthChanging;
    int tabBase;
    int tabSize;
    boolean wordWrap;
    int sel0;
    int sel1;
    Color unselected;
    Color selected;
    {
    }
}
