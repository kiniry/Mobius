package javax.swing.text.html;

import java.awt.*;
import java.text.BreakIterator;
import javax.swing.event.DocumentEvent;
import javax.swing.text.*;

public class InlineView extends LabelView {
    
    public InlineView(Element elem) {
        super(elem);
        StyleSheet sheet = getStyleSheet();
        attr = sheet.getViewAttributes(this);
    }
    
    public void insertUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        super.insertUpdate(e, a, f);
        longestWordSpan = -1.0F;
    }
    
    public void removeUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        super.removeUpdate(e, a, f);
        longestWordSpan = -1.0F;
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        super.changedUpdate(e, a, f);
        StyleSheet sheet = getStyleSheet();
        attr = sheet.getViewAttributes(this);
        longestWordSpan = -1.0F;
        preferenceChanged(null, true, true);
    }
    
    public AttributeSet getAttributes() {
        return attr;
    }
    
    public int getBreakWeight(int axis, float pos, float len) {
        if (nowrap) {
            return BadBreakWeight;
        }
        return super.getBreakWeight(axis, pos, len);
    }
    
    public View breakView(int axis, int offset, float pos, float len) {
        InlineView view = (InlineView)(InlineView)super.breakView(axis, offset, pos, len);
        if (view != this) {
            view.longestWordSpan = -1;
        }
        return view;
    }
    
    float getLongestWordSpan() {
        if (longestWordSpan < 0.0F) {
            longestWordSpan = calculateLongestWordSpan();
        }
        return longestWordSpan;
    }
    
    float calculateLongestWordSpan() {
        float rv = 0.0F;
        Document doc = getDocument();
        final Object MultiByteProperty = "multiByte";
        if (doc != null && Boolean.TRUE.equals(doc.getProperty(MultiByteProperty))) {
            rv = calculateLongestWordSpanUseBreakIterator();
        } else {
            rv = calculateLongestWordSpanUseWhitespace();
        }
        return rv;
    }
    
    float calculateLongestWordSpanUseBreakIterator() {
        float span = 0;
        Document doc = getDocument();
        int p0 = getStartOffset();
        int p1 = getEndOffset();
        if (p1 > p0) {
            try {
                FontMetrics metrics = getFontMetrics();
                Segment segment = new Segment();
                doc.getText(p0, p1 - p0, segment);
                Container c = getContainer();
                BreakIterator line;
                if (c != null) {
                    line = BreakIterator.getLineInstance(c.getLocale());
                } else {
                    line = BreakIterator.getLineInstance();
                }
                line.setText(segment);
                int start = line.first();
                for (int end = line.next(); end != BreakIterator.DONE; start = end, end = line.next()) {
                    if (end > start) {
                        span = Math.max(span, metrics.charsWidth(segment.array, start, end - start));
                    }
                }
            } catch (BadLocationException ble) {
            }
        }
        return span;
    }
    
    float calculateLongestWordSpanUseWhitespace() {
        float span = 0;
        Document doc = getDocument();
        int p0 = getStartOffset();
        int p1 = getEndOffset();
        if (p1 > p0) {
            try {
                Segment segment = new Segment();
                doc.getText(p0, p1 - p0, segment);
                final int CONTENT = 0;
                final int SPACES = 1;
                int state = CONTENT;
                int start = segment.offset;
                int end = start;
                FontMetrics metrics = getFontMetrics();
                final int lastIndex = segment.offset + segment.count - 1;
                for (int i = segment.offset; i <= lastIndex; i++) {
                    boolean updateSpan = false;
                    if (Character.isWhitespace(segment.array[i])) {
                        if (state == CONTENT) {
                            updateSpan = true;
                            state = SPACES;
                        }
                    } else {
                        if (state == SPACES) {
                            start = i;
                            end = start;
                            state = CONTENT;
                        } else {
                            end = i;
                        }
                        if (i == lastIndex) {
                            updateSpan = true;
                        }
                    }
                    if (updateSpan) {
                        if (end > start) {
                            span = Math.max(span, metrics.charsWidth(segment.array, start, end - start + 1));
                        }
                    }
                }
            } catch (BadLocationException ble) {
            }
        }
        return span;
    }
    
    protected void setPropertiesFromAttributes() {
        super.setPropertiesFromAttributes();
        AttributeSet a = getAttributes();
        Object decor = a.getAttribute(CSS$Attribute.TEXT_DECORATION);
        boolean u = (decor != null) ? (decor.toString().indexOf("underline") >= 0) : false;
        setUnderline(u);
        boolean s = (decor != null) ? (decor.toString().indexOf("line-through") >= 0) : false;
        setStrikeThrough(s);
        Object vAlign = a.getAttribute(CSS$Attribute.VERTICAL_ALIGN);
        s = (vAlign != null) ? (vAlign.toString().indexOf("sup") >= 0) : false;
        setSuperscript(s);
        s = (vAlign != null) ? (vAlign.toString().indexOf("sub") >= 0) : false;
        setSubscript(s);
        Object whitespace = a.getAttribute(CSS$Attribute.WHITE_SPACE);
        if ((whitespace != null) && whitespace.equals("nowrap")) {
            nowrap = true;
        } else {
            nowrap = false;
        }
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)getDocument();
        Color bg = doc.getBackground(a);
        if (bg != null) {
            setBackground(bg);
        }
    }
    
    protected StyleSheet getStyleSheet() {
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)getDocument();
        return doc.getStyleSheet();
    }
    private boolean nowrap;
    private AttributeSet attr;
    private float longestWordSpan = -1.0F;
}
