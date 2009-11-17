package javax.swing.text;

import java.awt.*;
import java.text.BreakIterator;
import javax.swing.event.*;
import java.util.BitSet;
import com.sun.java.swing.SwingUtilities2;

public class GlyphView extends View implements TabableView, Cloneable {
    
    public GlyphView(Element elem) {
        super(elem);
        offset = 0;
        length = 0;
        Element parent = elem.getParentElement();
        AttributeSet attr = elem.getAttributes();
        impliedCR = (attr != null && attr.getAttribute(IMPLIED_CR) != null && parent != null && parent.getElementCount() > 1);
        skipWidth = elem.getName().equals("br");
    }
    
    protected final Object clone() {
        Object o;
        try {
            o = super.clone();
        } catch (CloneNotSupportedException cnse) {
            o = null;
        }
        return o;
    }
    
    public GlyphView$GlyphPainter getGlyphPainter() {
        return painter;
    }
    
    public void setGlyphPainter(GlyphView$GlyphPainter p) {
        painter = p;
    }
    
    public Segment getText(int p0, int p1) {
        Segment text = SegmentCache.getSharedSegment();
        try {
            Document doc = getDocument();
            doc.getText(p0, p1 - p0, text);
        } catch (BadLocationException bl) {
            throw new StateInvariantError("GlyphView: Stale view: " + bl);
        }
        return text;
    }
    
    public Color getBackground() {
        Document doc = getDocument();
        if (doc instanceof StyledDocument) {
            AttributeSet attr = getAttributes();
            if (attr.isDefined(StyleConstants.Background)) {
                return ((StyledDocument)(StyledDocument)doc).getBackground(attr);
            }
        }
        return null;
    }
    
    public Color getForeground() {
        Document doc = getDocument();
        if (doc instanceof StyledDocument) {
            AttributeSet attr = getAttributes();
            return ((StyledDocument)(StyledDocument)doc).getForeground(attr);
        }
        Component c = getContainer();
        if (c != null) {
            return c.getForeground();
        }
        return null;
    }
    
    public Font getFont() {
        Document doc = getDocument();
        if (doc instanceof StyledDocument) {
            AttributeSet attr = getAttributes();
            return ((StyledDocument)(StyledDocument)doc).getFont(attr);
        }
        Component c = getContainer();
        if (c != null) {
            return c.getFont();
        }
        return null;
    }
    
    public boolean isUnderline() {
        AttributeSet attr = getAttributes();
        return StyleConstants.isUnderline(attr);
    }
    
    public boolean isStrikeThrough() {
        AttributeSet attr = getAttributes();
        return StyleConstants.isStrikeThrough(attr);
    }
    
    public boolean isSubscript() {
        AttributeSet attr = getAttributes();
        return StyleConstants.isSubscript(attr);
    }
    
    public boolean isSuperscript() {
        AttributeSet attr = getAttributes();
        return StyleConstants.isSuperscript(attr);
    }
    
    public TabExpander getTabExpander() {
        return expander;
    }
    
    protected void checkPainter() {
        if (painter == null) {
            if (defaultPainter == null) {
                String classname = "javax.swing.text.GlyphPainter1";
                try {
                    Class c;
                    ClassLoader loader = getClass().getClassLoader();
                    if (loader != null) {
                        c = loader.loadClass(classname);
                    } else {
                        c = Class.forName(classname);
                    }
                    Object o = c.newInstance();
                    if (o instanceof GlyphView$GlyphPainter) {
                        defaultPainter = (GlyphView$GlyphPainter)(GlyphView$GlyphPainter)o;
                    }
                } catch (Throwable e) {
                    throw new StateInvariantError("GlyphView: Can\'t load glyph painter: " + classname);
                }
            }
            setGlyphPainter(defaultPainter.getPainter(this, getStartOffset(), getEndOffset()));
        }
    }
    
    public float getTabbedSpan(float x, TabExpander e) {
        checkPainter();
        TabExpander old = expander;
        expander = e;
        if (expander != old) {
            preferenceChanged(null, true, false);
        }
        this.x = (int)x;
        int p0 = getStartOffset();
        int p1 = getEndOffset();
        float width = painter.getSpan(this, p0, p1, expander, x);
        return width;
    }
    
    public float getPartialSpan(int p0, int p1) {
        checkPainter();
        float width = painter.getSpan(this, p0, p1, expander, x);
        return width;
    }
    
    public int getStartOffset() {
        Element e = getElement();
        return (length > 0) ? e.getStartOffset() + offset : e.getStartOffset();
    }
    
    public int getEndOffset() {
        Element e = getElement();
        return (length > 0) ? e.getStartOffset() + offset + length : e.getEndOffset();
    }
    
    private void initSelections(int p0, int p1) {
        int viewPosCount = p1 - p0 + 1;
        if (selections == null || viewPosCount > selections.length) {
            selections = new byte[viewPosCount];
            return;
        }
        for (int i = 0; i < viewPosCount; selections[i++] = 0) ;
    }
    
    public void paint(Graphics g, Shape a) {
        checkPainter();
        boolean paintedText = false;
        Component c = getContainer();
        int p0 = getStartOffset();
        int p1 = getEndOffset();
        Rectangle alloc = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
        Color bg = getBackground();
        Color fg = getForeground();
        if (c instanceof JTextComponent) {
            JTextComponent tc = (JTextComponent)(JTextComponent)c;
            if (!tc.isEnabled()) {
                fg = tc.getDisabledTextColor();
            }
        }
        if (bg != null) {
            g.setColor(bg);
            g.fillRect(alloc.x, alloc.y, alloc.width, alloc.height);
        }
        if (c instanceof JTextComponent) {
            JTextComponent tc = (JTextComponent)(JTextComponent)c;
            Highlighter h = tc.getHighlighter();
            if (h instanceof LayeredHighlighter) {
                ((LayeredHighlighter)(LayeredHighlighter)h).paintLayeredHighlights(g, p0, p1, a, tc, this);
            }
        }
        if (Utilities.isComposedTextElement(getElement())) {
            Utilities.paintComposedText(g, a.getBounds(), this);
            paintedText = true;
        } else if (c instanceof JTextComponent) {
            JTextComponent tc = (JTextComponent)(JTextComponent)c;
            Color selFG = tc.getSelectedTextColor();
            if ((tc.getHighlighter() != null) && (selFG != null) && !selFG.equals(fg)) {
                Highlighter$Highlight[] h = tc.getHighlighter().getHighlights();
                if (h.length != 0) {
                    boolean initialized = false;
                    int viewSelectionCount = 0;
                    for (int i = 0; i < h.length; i++) {
                        Highlighter$Highlight highlight = h[i];
                        int hStart = highlight.getStartOffset();
                        int hEnd = highlight.getEndOffset();
                        if (hStart > p1 || hEnd < p0) {
                            continue;
                        }
                        if (!SwingUtilities2.useSelectedTextColor(highlight, tc)) {
                            continue;
                        }
                        if (hStart <= p0 && hEnd >= p1) {
                            paintTextUsingColor(g, a, selFG, p0, p1);
                            paintedText = true;
                            break;
                        }
                        if (!initialized) {
                            initSelections(p0, p1);
                            initialized = true;
                        }
                        hStart = Math.max(p0, hStart);
                        hEnd = Math.min(p1, hEnd);
                        paintTextUsingColor(g, a, selFG, hStart, hEnd);
                        selections[hStart - p0]++;
                        selections[hEnd - p0]--;
                        viewSelectionCount++;
                    }
                    if (!paintedText && viewSelectionCount > 0) {
                        int curPos = -1;
                        int startPos = 0;
                        int viewLen = p1 - p0;
                        while (curPos++ < viewLen) {
                            while (curPos < viewLen && selections[curPos] == 0) curPos++;
                            if (startPos != curPos) {
                                paintTextUsingColor(g, a, fg, p0 + startPos, p0 + curPos);
                            }
                            int checkSum = 0;
                            while (curPos < viewLen && (checkSum += selections[curPos]) != 0) curPos++;
                            startPos = curPos;
                        }
                        paintedText = true;
                    }
                }
            }
        }
        if (!paintedText) paintTextUsingColor(g, a, fg, p0, p1);
    }
    
    final void paintTextUsingColor(Graphics g, Shape a, Color c, int p0, int p1) {
        g.setColor(c);
        painter.paint(this, g, a, p0, p1);
        boolean underline = isUnderline();
        boolean strike = isStrikeThrough();
        if (underline || strike) {
            Rectangle alloc = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
            View parent = getParent();
            if ((parent != null) && (parent.getEndOffset() == p1)) {
                Segment s = getText(p0, p1);
                while ((s.count > 0) && (Character.isWhitespace(s.array[s.count - 1]))) {
                    p1 -= 1;
                    s.count -= 1;
                }
                SegmentCache.releaseSharedSegment(s);
            }
            int x0 = alloc.x;
            int p = getStartOffset();
            if (p != p0) {
                x0 += (int)painter.getSpan(this, p, p0, getTabExpander(), x0);
            }
            int x1 = x0 + (int)painter.getSpan(this, p0, p1, getTabExpander(), x0);
            int d = (int)painter.getDescent(this);
            int y = alloc.y + alloc.height - (int)painter.getDescent(this);
            if (underline) {
                int yTmp = y;
                yTmp += 1;
                g.drawLine(x0, yTmp, x1, yTmp);
            }
            if (strike) {
                int yTmp = y;
                yTmp -= (int)(painter.getAscent(this) * 0.3F);
                g.drawLine(x0, yTmp, x1, yTmp);
            }
        }
    }
    
    public float getPreferredSpan(int axis) {
        if (impliedCR) {
            return 0;
        }
        checkPainter();
        int p0 = getStartOffset();
        int p1 = getEndOffset();
        switch (axis) {
        case View.X_AXIS: 
            if (skipWidth) {
                return 0;
            }
            return painter.getSpan(this, p0, p1, expander, this.x);
        
        case View.Y_AXIS: 
            float h = painter.getHeight(this);
            if (isSuperscript()) {
                h += h / 3;
            }
            return h;
        
        default: 
            throw new IllegalArgumentException("Invalid axis: " + axis);
        
        }
    }
    
    public float getAlignment(int axis) {
        checkPainter();
        if (axis == View.Y_AXIS) {
            boolean sup = isSuperscript();
            boolean sub = isSubscript();
            float h = painter.getHeight(this);
            float d = painter.getDescent(this);
            float a = painter.getAscent(this);
            float align;
            if (sup) {
                align = 1.0F;
            } else if (sub) {
                align = (h > 0) ? (h - (d + (a / 2))) / h : 0;
            } else {
                align = (h > 0) ? (h - d) / h : 0;
            }
            return align;
        }
        return super.getAlignment(axis);
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        checkPainter();
        return painter.modelToView(this, pos, b, a);
    }
    
    public int viewToModel(float x, float y, Shape a, Position$Bias[] biasReturn) {
        checkPainter();
        return painter.viewToModel(this, x, y, a, biasReturn);
    }
    
    public int getBreakWeight(int axis, float pos, float len) {
        if (axis == View.X_AXIS) {
            checkPainter();
            int p0 = getStartOffset();
            int p1 = painter.getBoundedPosition(this, p0, pos, len);
            if (p1 == p0) {
                return View.BadBreakWeight;
            }
            if (getBreakSpot(p0, p1) != -1) {
                return View.ExcellentBreakWeight;
            }
            if (p1 == getEndOffset()) {
                return View.GoodBreakWeight;
            } else {
                return View.GoodBreakWeight - 1;
            }
        }
        return super.getBreakWeight(axis, pos, len);
    }
    
    public View breakView(int axis, int p0, float pos, float len) {
        if (axis == View.X_AXIS) {
            checkPainter();
            int p1 = painter.getBoundedPosition(this, p0, pos, len);
            int breakSpot = getBreakSpot(p0, p1);
            if (breakSpot != -1) {
                p1 = breakSpot;
            }
            if (p0 == getStartOffset() && p1 == getEndOffset()) {
                return this;
            }
            GlyphView v = (GlyphView)(GlyphView)createFragment(p0, p1);
            v.x = (int)pos;
            return v;
        }
        return this;
    }
    
    private int getBreakSpot(int p0, int p1) {
        Document doc = getDocument();
        if (doc != null && Boolean.TRUE.equals(doc.getProperty(AbstractDocument.MultiByteProperty))) {
            return getBreakSpotUseBreakIterator(p0, p1);
        }
        return getBreakSpotUseWhitespace(p0, p1);
    }
    
    private int getBreakSpotUseWhitespace(int p0, int p1) {
        Segment s = getText(p0, p1);
        for (char ch = s.last(); ch != Segment.DONE; ch = s.previous()) {
            if (Character.isWhitespace(ch)) {
                SegmentCache.releaseSharedSegment(s);
                return s.getIndex() - s.getBeginIndex() + 1 + p0;
            }
        }
        SegmentCache.releaseSharedSegment(s);
        return -1;
    }
    
    private int getBreakSpotUseBreakIterator(int p0, int p1) {
        Element parent = getElement().getParentElement();
        int parent0;
        int parent1;
        Container c = getContainer();
        BreakIterator breaker;
        if (parent == null) {
            parent0 = p0;
            parent1 = p1;
        } else {
            parent0 = parent.getStartOffset();
            parent1 = parent.getEndOffset();
        }
        if (c != null) {
            breaker = BreakIterator.getLineInstance(c.getLocale());
        } else {
            breaker = BreakIterator.getLineInstance();
        }
        Segment s = getText(parent0, parent1);
        int breakPoint;
        s.first();
        breaker.setText(s);
        if (p1 == parent1) {
            breakPoint = breaker.last();
        } else if (p1 + 1 == parent1) {
            breakPoint = breaker.next(s.offset + s.count - 2);
            if (breakPoint >= s.count + s.offset) {
                breakPoint = breaker.preceding(s.offset + s.count - 1);
            }
        } else {
            breakPoint = breaker.preceding(p1 - parent0 + s.offset + 1);
        }
        int retValue = -1;
        if (breakPoint != BreakIterator.DONE) {
            breakPoint = breakPoint - s.offset + parent0;
            if (breakPoint > p0) {
                if (p0 == parent0 && breakPoint == p0) {
                    retValue = -1;
                } else if (breakPoint <= p1) {
                    retValue = breakPoint;
                }
            }
        }
        SegmentCache.releaseSharedSegment(s);
        return retValue;
    }
    
    public View createFragment(int p0, int p1) {
        checkPainter();
        Element elem = getElement();
        GlyphView v = (GlyphView)(GlyphView)clone();
        v.offset = p0 - elem.getStartOffset();
        v.length = p1 - p0;
        v.painter = painter.getPainter(v, p0, p1);
        v.justificationInfo = null;
        return v;
    }
    
    public int getNextVisualPositionFrom(int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet) throws BadLocationException {
        return painter.getNextVisualPositionFrom(this, pos, b, a, direction, biasRet);
    }
    
    public void insertUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        justificationInfo = null;
        syncCR();
        preferenceChanged(null, true, false);
    }
    
    public void removeUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        justificationInfo = null;
        syncCR();
        preferenceChanged(null, true, false);
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        syncCR();
        preferenceChanged(null, true, true);
    }
    
    private void syncCR() {
        if (impliedCR) {
            Element parent = getElement().getParentElement();
            impliedCR = (parent != null && parent.getElementCount() > 1);
        }
    }
    {
    }
    
    GlyphView$JustificationInfo getJustificationInfo(int rowStartOffset) {
        if (justificationInfo != null) {
            return justificationInfo;
        }
        final int TRAILING = 0;
        final int CONTENT = 1;
        final int SPACES = 2;
        int startOffset = getStartOffset();
        int endOffset = getEndOffset();
        Segment segment = getText(startOffset, endOffset);
        int txtOffset = segment.offset;
        int txtEnd = segment.offset + segment.count - 1;
        int startContentPosition = txtEnd + 1;
        int endContentPosition = txtOffset - 1;
        int lastTabPosition = txtOffset - 1;
        int trailingSpaces = 0;
        int contentSpaces = 0;
        int leadingSpaces = 0;
        boolean hasTab = false;
        BitSet spaceMap = new BitSet(endOffset - startOffset + 1);
        for (int i = txtEnd, state = TRAILING; i >= txtOffset; i--) {
            if (' ' == segment.array[i]) {
                spaceMap.set(i - txtOffset);
                if (state == TRAILING) {
                    trailingSpaces++;
                } else if (state == CONTENT) {
                    state = SPACES;
                    leadingSpaces = 1;
                } else if (state == SPACES) {
                    leadingSpaces++;
                }
            } else if ('\t' == segment.array[i]) {
                hasTab = true;
                break;
            } else {
                if (state == TRAILING) {
                    if ('\n' != segment.array[i] && '\r' != segment.array[i]) {
                        state = CONTENT;
                        endContentPosition = i;
                    }
                } else if (state == CONTENT) {
                } else if (state == SPACES) {
                    contentSpaces += leadingSpaces;
                    leadingSpaces = 0;
                }
                startContentPosition = i;
            }
        }
        SegmentCache.releaseSharedSegment(segment);
        int startJustifiableContent = -1;
        if (startContentPosition < txtEnd) {
            startJustifiableContent = startContentPosition - txtOffset;
        }
        int endJustifiableContent = -1;
        if (endContentPosition > txtOffset) {
            endJustifiableContent = endContentPosition - txtOffset;
        }
        justificationInfo = new GlyphView$JustificationInfo(startJustifiableContent, endJustifiableContent, leadingSpaces, contentSpaces, trailingSpaces, hasTab, spaceMap);
        return justificationInfo;
    }
    private byte[] selections = null;
    int offset;
    int length;
    boolean impliedCR;
    private static final String IMPLIED_CR = "CR";
    boolean skipWidth;
    TabExpander expander;
    int x;
    GlyphView$GlyphPainter painter;
    static GlyphView$GlyphPainter defaultPainter;
    private GlyphView$JustificationInfo justificationInfo = null;
    {
    }
}
