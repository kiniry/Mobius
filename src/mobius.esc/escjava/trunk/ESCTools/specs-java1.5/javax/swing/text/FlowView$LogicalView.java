package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

class FlowView$LogicalView extends CompositeView {
    
    FlowView$LogicalView(Element elem) {
        super(elem);
    }
    
    protected int getViewIndexAtPosition(int pos) {
        Element elem = getElement();
        if (elem.isLeaf()) {
            return 0;
        }
        return super.getViewIndexAtPosition(pos);
    }
    
    protected void loadChildren(ViewFactory f) {
        Element elem = getElement();
        if (elem.isLeaf()) {
            View v = new LabelView(elem);
            append(v);
        } else {
            super.loadChildren(f);
        }
    }
    
    public AttributeSet getAttributes() {
        View p = getParent();
        return (p != null) ? p.getAttributes() : null;
    }
    
    public float getPreferredSpan(int axis) {
        float maxpref = 0;
        float pref = 0;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            pref += v.getPreferredSpan(axis);
            if (v.getBreakWeight(axis, 0, Integer.MAX_VALUE) >= ForcedBreakWeight) {
                maxpref = Math.max(maxpref, pref);
                pref = 0;
            }
        }
        maxpref = Math.max(maxpref, pref);
        return maxpref;
    }
    
    public float getMinimumSpan(int axis) {
        float maxmin = 0;
        float min = 0;
        boolean nowrap = false;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            if (v.getBreakWeight(axis, 0, Integer.MAX_VALUE) == BadBreakWeight) {
                min += v.getPreferredSpan(axis);
                nowrap = true;
            } else if (nowrap) {
                maxmin = Math.max(min, maxmin);
                nowrap = false;
                min = 0;
            }
        }
        maxmin = Math.max(maxmin, min);
        return maxmin;
    }
    
    protected void forwardUpdateToView(View v, DocumentEvent e, Shape a, ViewFactory f) {
        v.setParent(this);
        super.forwardUpdateToView(v, e, a, f);
    }
    
    public void paint(Graphics g, Shape allocation) {
    }
    
    protected boolean isBefore(int x, int y, Rectangle alloc) {
        return false;
    }
    
    protected boolean isAfter(int x, int y, Rectangle alloc) {
        return false;
    }
    
    protected View getViewAtPoint(int x, int y, Rectangle alloc) {
        return null;
    }
    
    protected void childAllocation(int index, Rectangle a) {
    }
}
