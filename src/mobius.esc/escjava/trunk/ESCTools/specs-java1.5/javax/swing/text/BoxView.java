package javax.swing.text;

import java.awt.*;
import javax.swing.event.DocumentEvent;
import javax.swing.SizeRequirements;

public class BoxView extends CompositeView {
    
    public BoxView(Element elem, int axis) {
        super(elem);
        tempRect = new Rectangle();
        this.majorAxis = axis;
        majorOffsets = new int[0];
        majorSpans = new int[0];
        majorReqValid = false;
        majorAllocValid = false;
        minorOffsets = new int[0];
        minorSpans = new int[0];
        minorReqValid = false;
        minorAllocValid = false;
    }
    
    public int getAxis() {
        return majorAxis;
    }
    
    public void setAxis(int axis) {
        boolean axisChanged = (axis != majorAxis);
        majorAxis = axis;
        if (axisChanged) {
            preferenceChanged(null, true, true);
        }
    }
    
    public void layoutChanged(int axis) {
        if (axis == majorAxis) {
            majorAllocValid = false;
        } else {
            minorAllocValid = false;
        }
    }
    
    protected boolean isLayoutValid(int axis) {
        if (axis == majorAxis) {
            return majorAllocValid;
        } else {
            return minorAllocValid;
        }
    }
    
    protected void paintChild(Graphics g, Rectangle alloc, int index) {
        View child = getView(index);
        child.paint(g, alloc);
    }
    
    public void replace(int index, int length, View[] elems) {
        super.replace(index, length, elems);
        int nInserted = (elems != null) ? elems.length : 0;
        majorOffsets = updateLayoutArray(majorOffsets, index, nInserted);
        majorSpans = updateLayoutArray(majorSpans, index, nInserted);
        majorReqValid = false;
        majorAllocValid = false;
        minorOffsets = updateLayoutArray(minorOffsets, index, nInserted);
        minorSpans = updateLayoutArray(minorSpans, index, nInserted);
        minorReqValid = false;
        minorAllocValid = false;
    }
    
    int[] updateLayoutArray(int[] oldArray, int offset, int nInserted) {
        int n = getViewCount();
        int[] newArray = new int[n];
        System.arraycopy(oldArray, 0, newArray, 0, offset);
        System.arraycopy(oldArray, offset, newArray, offset + nInserted, n - nInserted - offset);
        return newArray;
    }
    
    protected void forwardUpdate(DocumentEvent$ElementChange ec, DocumentEvent e, Shape a, ViewFactory f) {
        boolean wasValid = isLayoutValid(majorAxis);
        super.forwardUpdate(ec, e, a, f);
        if (wasValid && (!isLayoutValid(majorAxis))) {
            Component c = getContainer();
            if ((a != null) && (c != null)) {
                int pos = e.getOffset();
                int index = getViewIndexAtPosition(pos);
                Rectangle alloc = getInsideAllocation(a);
                if (majorAxis == X_AXIS) {
                    alloc.x += majorOffsets[index];
                    alloc.width -= majorOffsets[index];
                } else {
                    alloc.y += minorOffsets[index];
                    alloc.height -= minorOffsets[index];
                }
                c.repaint(alloc.x, alloc.y, alloc.width, alloc.height);
            }
        }
    }
    
    public void preferenceChanged(View child, boolean width, boolean height) {
        boolean majorChanged = (majorAxis == X_AXIS) ? width : height;
        boolean minorChanged = (majorAxis == X_AXIS) ? height : width;
        if (majorChanged) {
            majorReqValid = false;
            majorAllocValid = false;
        }
        if (minorChanged) {
            minorReqValid = false;
            minorAllocValid = false;
        }
        super.preferenceChanged(child, width, height);
    }
    
    public int getResizeWeight(int axis) {
        checkRequests(axis);
        if (axis == majorAxis) {
            if ((majorRequest.preferred != majorRequest.minimum) || (majorRequest.preferred != majorRequest.maximum)) {
                return 1;
            }
        } else {
            if ((minorRequest.preferred != minorRequest.minimum) || (minorRequest.preferred != minorRequest.maximum)) {
                return 1;
            }
        }
        return 0;
    }
    
    void setSpanOnAxis(int axis, float span) {
        if (axis == majorAxis) {
            if (majorSpan != (int)span) {
                majorAllocValid = false;
            }
            if (!majorAllocValid) {
                majorSpan = (int)span;
                checkRequests(majorAxis);
                layoutMajorAxis(majorSpan, axis, majorOffsets, majorSpans);
                majorAllocValid = true;
                updateChildSizes();
            }
        } else {
            if (((int)span) != minorSpan) {
                minorAllocValid = false;
            }
            if (!minorAllocValid) {
                minorSpan = (int)span;
                checkRequests(axis);
                layoutMinorAxis(minorSpan, axis, minorOffsets, minorSpans);
                minorAllocValid = true;
                updateChildSizes();
            }
        }
    }
    
    void updateChildSizes() {
        int n = getViewCount();
        if (majorAxis == X_AXIS) {
            for (int i = 0; i < n; i++) {
                View v = getView(i);
                v.setSize((float)majorSpans[i], (float)minorSpans[i]);
            }
        } else {
            for (int i = 0; i < n; i++) {
                View v = getView(i);
                v.setSize((float)minorSpans[i], (float)majorSpans[i]);
            }
        }
    }
    
    float getSpanOnAxis(int axis) {
        if (axis == majorAxis) {
            return majorSpan;
        } else {
            return minorSpan;
        }
    }
    
    public void setSize(float width, float height) {
        layout((int)(width - getLeftInset() - getRightInset()), (int)(height - getTopInset() - getBottomInset()));
    }
    
    public void paint(Graphics g, Shape allocation) {
        Rectangle alloc = (allocation instanceof Rectangle) ? (Rectangle)(Rectangle)allocation : allocation.getBounds();
        int n = getViewCount();
        int x = alloc.x + getLeftInset();
        int y = alloc.y + getTopInset();
        Rectangle clip = g.getClipBounds();
        for (int i = 0; i < n; i++) {
            tempRect.x = x + getOffset(X_AXIS, i);
            tempRect.y = y + getOffset(Y_AXIS, i);
            tempRect.width = getSpan(X_AXIS, i);
            tempRect.height = getSpan(Y_AXIS, i);
            if (tempRect.intersects(clip)) {
                paintChild(g, tempRect, i);
            }
        }
    }
    
    public Shape getChildAllocation(int index, Shape a) {
        if (a != null) {
            Shape ca = super.getChildAllocation(index, a);
            if ((ca != null) && (!isAllocationValid())) {
                Rectangle r = (ca instanceof Rectangle) ? (Rectangle)(Rectangle)ca : ca.getBounds();
                if ((r.width == 0) && (r.height == 0)) {
                    return null;
                }
            }
            return ca;
        }
        return null;
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        if (!isAllocationValid()) {
            Rectangle alloc = a.getBounds();
            setSize(alloc.width, alloc.height);
        }
        return super.modelToView(pos, a, b);
    }
    
    public int viewToModel(float x, float y, Shape a, Position$Bias[] bias) {
        if (!isAllocationValid()) {
            Rectangle alloc = a.getBounds();
            setSize(alloc.width, alloc.height);
        }
        return super.viewToModel(x, y, a, bias);
    }
    
    public float getAlignment(int axis) {
        checkRequests(axis);
        if (axis == majorAxis) {
            return majorRequest.alignment;
        } else {
            return minorRequest.alignment;
        }
    }
    
    public float getPreferredSpan(int axis) {
        checkRequests(axis);
        float marginSpan = (axis == X_AXIS) ? getLeftInset() + getRightInset() : getTopInset() + getBottomInset();
        if (axis == majorAxis) {
            return ((float)majorRequest.preferred) + marginSpan;
        } else {
            return ((float)minorRequest.preferred) + marginSpan;
        }
    }
    
    public float getMinimumSpan(int axis) {
        checkRequests(axis);
        float marginSpan = (axis == X_AXIS) ? getLeftInset() + getRightInset() : getTopInset() + getBottomInset();
        if (axis == majorAxis) {
            return ((float)majorRequest.minimum) + marginSpan;
        } else {
            return ((float)minorRequest.minimum) + marginSpan;
        }
    }
    
    public float getMaximumSpan(int axis) {
        checkRequests(axis);
        float marginSpan = (axis == X_AXIS) ? getLeftInset() + getRightInset() : getTopInset() + getBottomInset();
        if (axis == majorAxis) {
            return ((float)majorRequest.maximum) + marginSpan;
        } else {
            return ((float)minorRequest.maximum) + marginSpan;
        }
    }
    
    protected boolean isAllocationValid() {
        return (majorAllocValid && minorAllocValid);
    }
    
    protected boolean isBefore(int x, int y, Rectangle innerAlloc) {
        if (majorAxis == View.X_AXIS) {
            return (x < innerAlloc.x);
        } else {
            return (y < innerAlloc.y);
        }
    }
    
    protected boolean isAfter(int x, int y, Rectangle innerAlloc) {
        if (majorAxis == View.X_AXIS) {
            return (x > (innerAlloc.width + innerAlloc.x));
        } else {
            return (y > (innerAlloc.height + innerAlloc.y));
        }
    }
    
    protected View getViewAtPoint(int x, int y, Rectangle alloc) {
        int n = getViewCount();
        if (majorAxis == View.X_AXIS) {
            if (x < (alloc.x + majorOffsets[0])) {
                childAllocation(0, alloc);
                return getView(0);
            }
            for (int i = 0; i < n; i++) {
                if (x < (alloc.x + majorOffsets[i])) {
                    childAllocation(i - 1, alloc);
                    return getView(i - 1);
                }
            }
            childAllocation(n - 1, alloc);
            return getView(n - 1);
        } else {
            if (y < (alloc.y + majorOffsets[0])) {
                childAllocation(0, alloc);
                return getView(0);
            }
            for (int i = 0; i < n; i++) {
                if (y < (alloc.y + majorOffsets[i])) {
                    childAllocation(i - 1, alloc);
                    return getView(i - 1);
                }
            }
            childAllocation(n - 1, alloc);
            return getView(n - 1);
        }
    }
    
    protected void childAllocation(int index, Rectangle alloc) {
        alloc.x += getOffset(X_AXIS, index);
        alloc.y += getOffset(Y_AXIS, index);
        alloc.width = getSpan(X_AXIS, index);
        alloc.height = getSpan(Y_AXIS, index);
    }
    
    protected void layout(int width, int height) {
        setSpanOnAxis(X_AXIS, width);
        setSpanOnAxis(Y_AXIS, height);
    }
    
    public int getWidth() {
        int span;
        if (majorAxis == X_AXIS) {
            span = majorSpan;
        } else {
            span = minorSpan;
        }
        span += getLeftInset() - getRightInset();
        return span;
    }
    
    public int getHeight() {
        int span;
        if (majorAxis == Y_AXIS) {
            span = majorSpan;
        } else {
            span = minorSpan;
        }
        span += getTopInset() - getBottomInset();
        return span;
    }
    
    protected void layoutMajorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        long preferred = 0;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            spans[i] = (int)v.getPreferredSpan(axis);
            preferred += spans[i];
        }
        long desiredAdjustment = targetSpan - preferred;
        float adjustmentFactor = 0.0F;
        int[] diffs = null;
        if (desiredAdjustment != 0) {
            long totalSpan = 0;
            diffs = new int[n];
            for (int i = 0; i < n; i++) {
                View v = getView(i);
                int tmp;
                if (desiredAdjustment < 0) {
                    tmp = (int)v.getMinimumSpan(axis);
                    diffs[i] = spans[i] - tmp;
                } else {
                    tmp = (int)v.getMaximumSpan(axis);
                    diffs[i] = tmp - spans[i];
                }
                totalSpan += tmp;
            }
            float maximumAdjustment = Math.abs(totalSpan - preferred);
            adjustmentFactor = desiredAdjustment / maximumAdjustment;
            adjustmentFactor = Math.min(adjustmentFactor, 1.0F);
            adjustmentFactor = Math.max(adjustmentFactor, -1.0F);
        }
        int totalOffset = 0;
        for (int i = 0; i < n; i++) {
            offsets[i] = totalOffset;
            if (desiredAdjustment != 0) {
                float adjF = adjustmentFactor * diffs[i];
                spans[i] += Math.round(adjF);
            }
            totalOffset = (int)Math.min((long)totalOffset + (long)spans[i], Integer.MAX_VALUE);
        }
    }
    
    protected void layoutMinorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            int max = (int)v.getMaximumSpan(axis);
            if (max < targetSpan) {
                float align = v.getAlignment(axis);
                offsets[i] = (int)((targetSpan - max) * align);
                spans[i] = max;
            } else {
                int min = (int)v.getMinimumSpan(axis);
                offsets[i] = 0;
                spans[i] = Math.max(min, targetSpan);
            }
        }
    }
    
    protected SizeRequirements calculateMajorAxisRequirements(int axis, SizeRequirements r) {
        float min = 0;
        float pref = 0;
        float max = 0;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            min += v.getMinimumSpan(axis);
            pref += v.getPreferredSpan(axis);
            max += v.getMaximumSpan(axis);
        }
        if (r == null) {
            r = new SizeRequirements();
        }
        r.alignment = 0.5F;
        r.minimum = (int)min;
        r.preferred = (int)pref;
        r.maximum = (int)max;
        return r;
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        int min = 0;
        long pref = 0;
        int max = Integer.MAX_VALUE;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            min = Math.max((int)v.getMinimumSpan(axis), min);
            pref = Math.max((int)v.getPreferredSpan(axis), pref);
            max = Math.max((int)v.getMaximumSpan(axis), max);
        }
        if (r == null) {
            r = new SizeRequirements();
            r.alignment = 0.5F;
        }
        r.preferred = (int)pref;
        r.minimum = min;
        r.maximum = max;
        return r;
    }
    
    void checkRequests(int axis) {
        if ((axis != X_AXIS) && (axis != Y_AXIS)) {
            throw new IllegalArgumentException("Invalid axis: " + axis);
        }
        if (axis == majorAxis) {
            if (!majorReqValid) {
                majorRequest = calculateMajorAxisRequirements(axis, majorRequest);
                majorReqValid = true;
            }
        } else if (!minorReqValid) {
            minorRequest = calculateMinorAxisRequirements(axis, minorRequest);
            minorReqValid = true;
        }
    }
    
    protected void baselineLayout(int targetSpan, int axis, int[] offsets, int[] spans) {
        int totalAscent = (int)(targetSpan * getAlignment(axis));
        int totalDescent = targetSpan - totalAscent;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            float align = v.getAlignment(axis);
            int viewSpan;
            if (v.getResizeWeight(axis) > 0) {
                int minSpan = (int)v.getMinimumSpan(axis);
                int maxSpan = (int)v.getMaximumSpan(axis);
                if (align == 0.0F) {
                    viewSpan = Math.max(Math.min(maxSpan, totalDescent), minSpan);
                } else if (align == 1.0F) {
                    viewSpan = Math.max(Math.min(maxSpan, totalAscent), minSpan);
                } else {
                    int fitSpan = (int)Math.min(totalAscent / align, totalDescent / (1.0F - align));
                    viewSpan = Math.max(Math.min(maxSpan, fitSpan), minSpan);
                }
            } else {
                viewSpan = (int)v.getPreferredSpan(axis);
            }
            offsets[i] = totalAscent - (int)(viewSpan * align);
            spans[i] = viewSpan;
        }
    }
    
    protected SizeRequirements baselineRequirements(int axis, SizeRequirements r) {
        SizeRequirements totalAscent = new SizeRequirements();
        SizeRequirements totalDescent = new SizeRequirements();
        if (r == null) {
            r = new SizeRequirements();
        }
        r.alignment = 0.5F;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            float align = v.getAlignment(axis);
            int span;
            int ascent;
            int descent;
            span = (int)v.getPreferredSpan(axis);
            ascent = (int)(align * span);
            descent = span - ascent;
            totalAscent.preferred = Math.max(ascent, totalAscent.preferred);
            totalDescent.preferred = Math.max(descent, totalDescent.preferred);
            if (v.getResizeWeight(axis) > 0) {
                span = (int)v.getMinimumSpan(axis);
                ascent = (int)(align * span);
                descent = span - ascent;
                totalAscent.minimum = Math.max(ascent, totalAscent.minimum);
                totalDescent.minimum = Math.max(descent, totalDescent.minimum);
                span = (int)v.getMaximumSpan(axis);
                ascent = (int)(align * span);
                descent = span - ascent;
                totalAscent.maximum = Math.max(ascent, totalAscent.maximum);
                totalDescent.maximum = Math.max(descent, totalDescent.maximum);
            } else {
                totalAscent.minimum = Math.max(ascent, totalAscent.minimum);
                totalDescent.minimum = Math.max(descent, totalDescent.minimum);
                totalAscent.maximum = Math.max(ascent, totalAscent.maximum);
                totalDescent.maximum = Math.max(descent, totalDescent.maximum);
            }
        }
        r.preferred = (int)Math.min((long)totalAscent.preferred + (long)totalDescent.preferred, Integer.MAX_VALUE);
        if (r.preferred > 0) {
            r.alignment = (float)totalAscent.preferred / r.preferred;
        }
        if (r.alignment == 0.0F) {
            r.minimum = totalDescent.minimum;
            r.maximum = totalDescent.maximum;
        } else if (r.alignment == 1.0F) {
            r.minimum = totalAscent.minimum;
            r.maximum = totalAscent.maximum;
        } else {
            r.minimum = Math.max((int)(totalAscent.minimum / r.alignment), (int)(totalDescent.minimum / (1.0F - r.alignment)));
            r.maximum = Math.min((int)(totalAscent.maximum / r.alignment), (int)(totalDescent.maximum / (1.0F - r.alignment)));
        }
        return r;
    }
    
    protected int getOffset(int axis, int childIndex) {
        int[] offsets = (axis == majorAxis) ? majorOffsets : minorOffsets;
        return offsets[childIndex];
    }
    
    protected int getSpan(int axis, int childIndex) {
        int[] spans = (axis == majorAxis) ? majorSpans : minorSpans;
        return spans[childIndex];
    }
    
    protected boolean flipEastAndWestAtEnds(int position, Position$Bias bias) {
        if (majorAxis == Y_AXIS) {
            int testPos = (bias == Position$Bias.Backward) ? Math.max(0, position - 1) : position;
            int index = getViewIndexAtPosition(testPos);
            if (index != -1) {
                View v = getView(index);
                if (v != null && v instanceof CompositeView) {
                    return ((CompositeView)(CompositeView)v).flipEastAndWestAtEnds(position, bias);
                }
            }
        }
        return false;
    }
    int majorAxis;
    int majorSpan;
    int minorSpan;
    boolean majorReqValid;
    boolean minorReqValid;
    SizeRequirements majorRequest;
    SizeRequirements minorRequest;
    boolean majorAllocValid;
    int[] majorOffsets;
    int[] majorSpans;
    boolean minorAllocValid;
    int[] minorOffsets;
    int[] minorSpans;
    Rectangle tempRect;
}
