package javax.swing.text;

import java.util.Arrays;
import java.awt.*;
import javax.swing.event.*;
import javax.swing.SizeRequirements;

class ParagraphView$Row extends BoxView {
    /*synthetic*/ final ParagraphView this$0;
    
    ParagraphView$Row(/*synthetic*/ final ParagraphView this$0, Element elem) {
        super(elem, View.X_AXIS);
        this.this$0 = this$0;
    }
    
    protected void loadChildren(ViewFactory f) {
    }
    
    public AttributeSet getAttributes() {
        View p = getParent();
        return (p != null) ? p.getAttributes() : null;
    }
    
    public float getAlignment(int axis) {
        if (axis == View.X_AXIS) {
            switch (ParagraphView.access$000(this$0)) {
            case StyleConstants.ALIGN_LEFT: 
                return 0;
            
            case StyleConstants.ALIGN_RIGHT: 
                return 1;
            
            case StyleConstants.ALIGN_CENTER: 
                return 0.5F;
            
            case StyleConstants.ALIGN_JUSTIFIED: 
                float rv = 0.5F;
                if (isJustifiableDocument()) {
                    rv = 0.0F;
                }
                return rv;
            
            }
        }
        return super.getAlignment(axis);
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        Rectangle r = a.getBounds();
        View v = getViewAtPosition(pos, r);
        if ((v != null) && (!v.getElement().isLeaf())) {
            return super.modelToView(pos, a, b);
        }
        r = a.getBounds();
        int height = r.height;
        int y = r.y;
        Shape loc = super.modelToView(pos, a, b);
        r = loc.getBounds();
        r.height = height;
        r.y = y;
        return r;
    }
    
    public int getStartOffset() {
        int offs = Integer.MAX_VALUE;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            offs = Math.min(offs, v.getStartOffset());
        }
        return offs;
    }
    
    public int getEndOffset() {
        int offs = 0;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            offs = Math.max(offs, v.getEndOffset());
        }
        return offs;
    }
    
    protected void layoutMinorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        baselineLayout(targetSpan, axis, offsets, spans);
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        return baselineRequirements(axis, r);
    }
    
    private boolean isLastRow() {
        View parent;
        return ((parent = getParent()) == null || this == parent.getView(parent.getViewCount() - 1));
    }
    
    private boolean isBrokenRow() {
        boolean rv = false;
        int viewsCount = getViewCount();
        if (viewsCount > 0) {
            View lastView = getView(viewsCount - 1);
            if (lastView.getBreakWeight(X_AXIS, 0, 0) >= ForcedBreakWeight) {
                rv = true;
            }
        }
        return rv;
    }
    
    private boolean isJustifiableDocument() {
        return (!Boolean.TRUE.equals(getDocument().getProperty(AbstractDocument.I18NProperty)));
    }
    
    private boolean isJustifyEnabled() {
        boolean ret = (ParagraphView.access$000(this$0) == StyleConstants.ALIGN_JUSTIFIED);
        ret = ret && isJustifiableDocument();
        ret = ret && !isLastRow();
        ret = ret && !isBrokenRow();
        return ret;
    }
    
    protected SizeRequirements calculateMajorAxisRequirements(int axis, SizeRequirements r) {
        int[] oldJustficationData = justificationData;
        justificationData = null;
        SizeRequirements ret = super.calculateMajorAxisRequirements(axis, r);
        if (isJustifyEnabled()) {
            justificationData = oldJustficationData;
        }
        return ret;
    }
    
    protected void layoutMajorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        int[] oldJustficationData = justificationData;
        justificationData = null;
        super.layoutMajorAxis(targetSpan, axis, offsets, spans);
        if (!isJustifyEnabled()) {
            return;
        }
        int currentSpan = 0;
        for (int[] arr$ = spans, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            int span = arr$[i$];
            {
                currentSpan += span;
            }
        }
        if (currentSpan == targetSpan) {
            return;
        }
        int extendableSpaces = 0;
        int startJustifiableContent = -1;
        int endJustifiableContent = -1;
        int lastLeadingSpaces = 0;
        int rowStartOffset = getStartOffset();
        int rowEndOffset = getEndOffset();
        int[] spaceMap = new int[rowEndOffset - rowStartOffset];
        Arrays.fill(spaceMap, 0);
        for (int i = getViewCount() - 1; i >= 0; i--) {
            View view = getView(i);
            if (view instanceof GlyphView) {
                GlyphView$JustificationInfo justificationInfo = ((GlyphView)(GlyphView)view).getJustificationInfo(rowStartOffset);
                final int viewStartOffset = view.getStartOffset();
                final int offset = viewStartOffset - rowStartOffset;
                for (int j = 0; j < justificationInfo.spaceMap.length(); j++) {
                    if (justificationInfo.spaceMap.get(j)) {
                        spaceMap[j + offset] = 1;
                    }
                }
                if (startJustifiableContent > 0) {
                    if (justificationInfo.end >= 0) {
                        extendableSpaces += justificationInfo.trailingSpaces;
                    } else {
                        lastLeadingSpaces += justificationInfo.trailingSpaces;
                    }
                }
                if (justificationInfo.start >= 0) {
                    startJustifiableContent = justificationInfo.start + viewStartOffset;
                    extendableSpaces += lastLeadingSpaces;
                }
                if (justificationInfo.end >= 0 && endJustifiableContent < 0) {
                    endJustifiableContent = justificationInfo.end + viewStartOffset;
                }
                extendableSpaces += justificationInfo.contentSpaces;
                lastLeadingSpaces = justificationInfo.leadingSpaces;
                if (justificationInfo.hasTab) {
                    break;
                }
            }
        }
        if (extendableSpaces <= 0) {
            return;
        }
        int adjustment = (targetSpan - currentSpan);
        int spaceAddon = (extendableSpaces > 0) ? adjustment / extendableSpaces : 0;
        int spaceAddonLeftoverEnd = -1;
        for (int i = startJustifiableContent - rowStartOffset, leftover = adjustment - spaceAddon * extendableSpaces; leftover > 0; leftover -= spaceMap[i], i++) {
            spaceAddonLeftoverEnd = i;
        }
        if (spaceAddon > 0 || spaceAddonLeftoverEnd >= 0) {
            justificationData = (oldJustficationData != null) ? oldJustficationData : new int[END_JUSTIFIABLE + 1];
            justificationData[SPACE_ADDON] = spaceAddon;
            justificationData[SPACE_ADDON_LEFTOVER_END] = spaceAddonLeftoverEnd;
            justificationData[START_JUSTIFIABLE] = startJustifiableContent - rowStartOffset;
            justificationData[END_JUSTIFIABLE] = endJustifiableContent - rowStartOffset;
            super.layoutMajorAxis(targetSpan, axis, offsets, spans);
        }
    }
    
    public float getMaximumSpan(int axis) {
        float ret;
        if (View.X_AXIS == axis && isJustifyEnabled()) {
            ret = Float.MAX_VALUE;
        } else {
            ret = super.getMaximumSpan(axis);
        }
        return ret;
    }
    
    protected int getViewIndexAtPosition(int pos) {
        if (pos < getStartOffset() || pos >= getEndOffset()) return -1;
        for (int counter = getViewCount() - 1; counter >= 0; counter--) {
            View v = getView(counter);
            if (pos >= v.getStartOffset() && pos < v.getEndOffset()) {
                return counter;
            }
        }
        return -1;
    }
    
    protected short getLeftInset() {
        View parentView;
        int adjustment = 0;
        if ((parentView = getParent()) != null) {
            if (this == parentView.getView(0)) {
                adjustment = this$0.firstLineIndent;
            }
        }
        return (short)(super.getLeftInset() + adjustment);
    }
    
    protected short getBottomInset() {
        return (short)(super.getBottomInset() + ((minorRequest != null) ? minorRequest.preferred : 0) * ParagraphView.access$100(this$0));
    }
    static final int SPACE_ADDON = 0;
    static final int SPACE_ADDON_LEFTOVER_END = 1;
    static final int START_JUSTIFIABLE = 2;
    static final int END_JUSTIFIABLE = 3;
    int[] justificationData = null;
}
