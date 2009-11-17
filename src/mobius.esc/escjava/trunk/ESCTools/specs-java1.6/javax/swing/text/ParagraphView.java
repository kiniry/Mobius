package javax.swing.text;

import java.awt.*;
import java.awt.font.TextAttribute;
import javax.swing.event.*;

public class ParagraphView extends FlowView implements TabExpander {
    
    /*synthetic*/ static float access$100(ParagraphView x0) {
        return x0.lineSpacing;
    }
    
    /*synthetic*/ static int access$000(ParagraphView x0) {
        return x0.justification;
    }
    
    public ParagraphView(Element elem) {
        super(elem, View.Y_AXIS);
        setPropertiesFromAttributes();
        Document doc = elem.getDocument();
        Object i18nFlag = doc.getProperty(AbstractDocument.I18NProperty);
        if ((i18nFlag != null) && i18nFlag.equals(Boolean.TRUE)) {
            try {
                if (i18nStrategy == null) {
                    String classname = "javax.swing.text.TextLayoutStrategy";
                    ClassLoader loader = getClass().getClassLoader();
                    if (loader != null) {
                        i18nStrategy = loader.loadClass(classname);
                    } else {
                        i18nStrategy = Class.forName(classname);
                    }
                }
                Object o = i18nStrategy.newInstance();
                if (o instanceof FlowView$FlowStrategy) {
                    strategy = (FlowView$FlowStrategy)(FlowView$FlowStrategy)o;
                }
            } catch (Throwable e) {
                throw new StateInvariantError("ParagraphView: Can\'t create i18n strategy: " + e.getMessage());
            }
        }
    }
    
    protected void setJustification(int j) {
        justification = j;
    }
    
    protected void setLineSpacing(float ls) {
        lineSpacing = ls;
    }
    
    protected void setFirstLineIndent(float fi) {
        firstLineIndent = (int)fi;
    }
    
    protected void setPropertiesFromAttributes() {
        AttributeSet attr = getAttributes();
        if (attr != null) {
            setParagraphInsets(attr);
            Integer a = (Integer)(Integer)attr.getAttribute(StyleConstants.Alignment);
            int alignment;
            if (a == null) {
                Document doc = getElement().getDocument();
                Object o = doc.getProperty(TextAttribute.RUN_DIRECTION);
                if ((o != null) && o.equals(TextAttribute.RUN_DIRECTION_RTL)) {
                    alignment = StyleConstants.ALIGN_RIGHT;
                } else {
                    alignment = StyleConstants.ALIGN_LEFT;
                }
            } else {
                alignment = a.intValue();
            }
            setJustification(alignment);
            setLineSpacing(StyleConstants.getLineSpacing(attr));
            setFirstLineIndent(StyleConstants.getFirstLineIndent(attr));
        }
    }
    
    protected int getLayoutViewCount() {
        return layoutPool.getViewCount();
    }
    
    protected View getLayoutView(int index) {
        return layoutPool.getView(index);
    }
    
    protected void adjustRow(ParagraphView$Row r, int desiredSpan, int x) {
    }
    
    protected int getNextNorthSouthVisualPositionFrom(int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet) throws BadLocationException {
        int vIndex;
        if (pos == -1) {
            vIndex = (direction == NORTH) ? getViewCount() - 1 : 0;
        } else {
            if (b == Position$Bias.Backward && pos > 0) {
                vIndex = getViewIndexAtPosition(pos - 1);
            } else {
                vIndex = getViewIndexAtPosition(pos);
            }
            if (direction == NORTH) {
                if (vIndex == 0) {
                    return -1;
                }
                vIndex--;
            } else if (++vIndex >= getViewCount()) {
                return -1;
            }
        }
        JTextComponent text = (JTextComponent)(JTextComponent)getContainer();
        Caret c = text.getCaret();
        Point magicPoint;
        magicPoint = (c != null) ? c.getMagicCaretPosition() : null;
        int x;
        if (magicPoint == null) {
            Shape posBounds;
            try {
                posBounds = text.getUI().modelToView(text, pos, b);
            } catch (BadLocationException exc) {
                posBounds = null;
            }
            if (posBounds == null) {
                x = 0;
            } else {
                x = posBounds.getBounds().x;
            }
        } else {
            x = magicPoint.x;
        }
        return getClosestPositionTo(pos, b, a, direction, biasRet, vIndex, x);
    }
    
    protected int getClosestPositionTo(int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet, int rowIndex, int x) throws BadLocationException {
        JTextComponent text = (JTextComponent)(JTextComponent)getContainer();
        Document doc = getDocument();
        AbstractDocument aDoc = (doc instanceof AbstractDocument) ? (AbstractDocument)(AbstractDocument)doc : null;
        View row = getView(rowIndex);
        int lastPos = -1;
        biasRet[0] = Position$Bias.Forward;
        for (int vc = 0, numViews = row.getViewCount(); vc < numViews; vc++) {
            View v = row.getView(vc);
            int start = v.getStartOffset();
            boolean ltr = (aDoc != null) ? aDoc.isLeftToRight(start, start + 1) : true;
            if (ltr) {
                lastPos = start;
                for (int end = v.getEndOffset(); lastPos < end; lastPos++) {
                    float xx = text.modelToView(lastPos).getBounds().x;
                    if (xx >= x) {
                        while (++lastPos < end && text.modelToView(lastPos).getBounds().x == xx) {
                        }
                        return --lastPos;
                    }
                }
                lastPos--;
            } else {
                for (lastPos = v.getEndOffset() - 1; lastPos >= start; lastPos--) {
                    float xx = text.modelToView(lastPos).getBounds().x;
                    if (xx >= x) {
                        while (--lastPos >= start && text.modelToView(lastPos).getBounds().x == xx) {
                        }
                        return ++lastPos;
                    }
                }
                lastPos++;
            }
        }
        if (lastPos == -1) {
            return getStartOffset();
        }
        return lastPos;
    }
    
    protected boolean flipEastAndWestAtEnds(int position, Position$Bias bias) {
        Document doc = getDocument();
        if (doc instanceof AbstractDocument && !((AbstractDocument)(AbstractDocument)doc).isLeftToRight(getStartOffset(), getStartOffset() + 1)) {
            return true;
        }
        return false;
    }
    
    public int getFlowSpan(int index) {
        View child = getView(index);
        int adjust = 0;
        if (child instanceof ParagraphView$Row) {
            ParagraphView$Row row = (ParagraphView$Row)(ParagraphView$Row)child;
            adjust = row.getLeftInset() + row.getRightInset();
        }
        int span = layoutSpan - adjust;
        return span;
    }
    
    public int getFlowStart(int index) {
        View child = getView(index);
        int adjust = 0;
        if (child instanceof ParagraphView$Row) {
            ParagraphView$Row row = (ParagraphView$Row)(ParagraphView$Row)child;
            adjust = row.getLeftInset();
        }
        return tabBase + adjust;
    }
    
    protected View createRow() {
        return new ParagraphView$Row(this, getElement());
    }
    
    public float nextTabStop(float x, int tabOffset) {
        if (justification != StyleConstants.ALIGN_LEFT) return x + 10.0F;
        x -= tabBase;
        TabSet tabs = getTabSet();
        if (tabs == null) {
            return (float)(tabBase + (((int)x / 72 + 1) * 72));
        }
        TabStop tab = tabs.getTabAfter(x + 0.01F);
        if (tab == null) {
            return tabBase + x + 5.0F;
        }
        int alignment = tab.getAlignment();
        int offset;
        switch (alignment) {
        default: 
        
        case TabStop.ALIGN_LEFT: 
            return tabBase + tab.getPosition();
        
        case TabStop.ALIGN_BAR: 
            return tabBase + tab.getPosition();
        
        case TabStop.ALIGN_RIGHT: 
        
        case TabStop.ALIGN_CENTER: 
            offset = findOffsetToCharactersInString(tabChars, tabOffset + 1);
            break;
        
        case TabStop.ALIGN_DECIMAL: 
            offset = findOffsetToCharactersInString(tabDecimalChars, tabOffset + 1);
            break;
        
        }
        if (offset == -1) {
            offset = getEndOffset();
        }
        float charsSize = getPartialSize(tabOffset + 1, offset);
        switch (alignment) {
        case TabStop.ALIGN_RIGHT: 
        
        case TabStop.ALIGN_DECIMAL: 
            return tabBase + Math.max(x, tab.getPosition() - charsSize);
        
        case TabStop.ALIGN_CENTER: 
            return tabBase + Math.max(x, tab.getPosition() - charsSize / 2.0F);
        
        }
        return x;
    }
    
    protected TabSet getTabSet() {
        return StyleConstants.getTabSet(getElement().getAttributes());
    }
    
    protected float getPartialSize(int startOffset, int endOffset) {
        float size = 0.0F;
        int viewIndex;
        int numViews = getViewCount();
        View view;
        int viewEnd;
        int tempEnd;
        viewIndex = getElement().getElementIndex(startOffset);
        numViews = layoutPool.getViewCount();
        while (startOffset < endOffset && viewIndex < numViews) {
            view = layoutPool.getView(viewIndex++);
            viewEnd = view.getEndOffset();
            tempEnd = Math.min(endOffset, viewEnd);
            if (view instanceof TabableView) size += ((TabableView)(TabableView)view).getPartialSpan(startOffset, tempEnd); else if (startOffset == view.getStartOffset() && tempEnd == view.getEndOffset()) size += view.getPreferredSpan(View.X_AXIS); else return 0.0F;
            startOffset = viewEnd;
        }
        return size;
    }
    
    protected int findOffsetToCharactersInString(char[] string, int start) {
        int stringLength = string.length;
        int end = getEndOffset();
        Segment seg = new Segment();
        try {
            getDocument().getText(start, end - start, seg);
        } catch (BadLocationException ble) {
            return -1;
        }
        for (int counter = seg.offset, maxCounter = seg.offset + seg.count; counter < maxCounter; counter++) {
            char currentChar = seg.array[counter];
            for (int subCounter = 0; subCounter < stringLength; subCounter++) {
                if (currentChar == string[subCounter]) return counter - seg.offset + start;
            }
        }
        return -1;
    }
    
    protected float getTabBase() {
        return (float)tabBase;
    }
    
    public void paint(Graphics g, Shape a) {
        Rectangle alloc = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
        tabBase = alloc.x + getLeftInset();
        super.paint(g, a);
        if (firstLineIndent < 0) {
            Shape sh = getChildAllocation(0, a);
            if ((sh != null) && sh.intersects(alloc)) {
                int x = alloc.x + getLeftInset() + firstLineIndent;
                int y = alloc.y + getTopInset();
                Rectangle clip = g.getClipBounds();
                tempRect.x = x + getOffset(X_AXIS, 0);
                tempRect.y = y + getOffset(Y_AXIS, 0);
                tempRect.width = getSpan(X_AXIS, 0) - firstLineIndent;
                tempRect.height = getSpan(Y_AXIS, 0);
                if (tempRect.intersects(clip)) {
                    tempRect.x = tempRect.x - firstLineIndent;
                    paintChild(g, tempRect, 0);
                }
            }
        }
    }
    
    public float getAlignment(int axis) {
        switch (axis) {
        case Y_AXIS: 
            float a = 0.5F;
            if (getViewCount() != 0) {
                int paragraphSpan = (int)getPreferredSpan(View.Y_AXIS);
                View v = getView(0);
                int rowSpan = (int)v.getPreferredSpan(View.Y_AXIS);
                a = (paragraphSpan != 0) ? ((float)(rowSpan / 2)) / paragraphSpan : 0;
            }
            return a;
        
        case X_AXIS: 
            return 0.5F;
        
        default: 
            throw new IllegalArgumentException("Invalid axis: " + axis);
        
        }
    }
    
    public View breakView(int axis, float len, Shape a) {
        if (axis == View.Y_AXIS) {
            if (a != null) {
                Rectangle alloc = a.getBounds();
                setSize(alloc.width, alloc.height);
            }
            return this;
        }
        return this;
    }
    
    public int getBreakWeight(int axis, float len) {
        if (axis == View.Y_AXIS) {
            return BadBreakWeight;
        }
        return BadBreakWeight;
    }
    
    public void changedUpdate(DocumentEvent changes, Shape a, ViewFactory f) {
        setPropertiesFromAttributes();
        layoutChanged(X_AXIS);
        layoutChanged(Y_AXIS);
        super.changedUpdate(changes, a, f);
    }
    private int justification;
    private float lineSpacing;
    protected int firstLineIndent = 0;
    private int tabBase;
    static Class i18nStrategy;
    static char[] tabChars;
    static char[] tabDecimalChars;
    static {
        tabChars = new char[1];
        tabChars[0] = '\t';
        tabDecimalChars = new char[2];
        tabDecimalChars[0] = '\t';
        tabDecimalChars[1] = '.';
    }
    {
    }
}
