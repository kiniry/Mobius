package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;
import javax.swing.SizeRequirements;

public abstract class FlowView extends BoxView {
    private static final FlowView$FlowStrategy STRATEGY = new FlowView$FlowStrategy();
    
    public FlowView(Element elem, int axis) {
        super(elem, axis);
        layoutSpan = Integer.MAX_VALUE;
        strategy = STRATEGY;
    }
    
    public int getFlowAxis() {
        if (getAxis() == Y_AXIS) {
            return X_AXIS;
        }
        return Y_AXIS;
    }
    
    public int getFlowSpan(int index) {
        return layoutSpan;
    }
    
    public int getFlowStart(int index) {
        return 0;
    }
    
    protected abstract View createRow();
    
    protected void loadChildren(ViewFactory f) {
        if (layoutPool == null) {
            layoutPool = new FlowView$LogicalView(getElement());
        }
        layoutPool.setParent(this);
        strategy.insertUpdate(this, null, null);
    }
    
    protected int getViewIndexAtPosition(int pos) {
        if (pos >= getStartOffset() && (pos < getEndOffset())) {
            for (int counter = getViewCount() - 1; counter >= 0; counter--) {
                View v = getView(counter);
                if (pos >= v.getStartOffset() && pos < v.getEndOffset()) {
                    return counter;
                }
            }
        }
        return -1;
    }
    
    protected void layout(int width, int height) {
        final int faxis = getFlowAxis();
        int newSpan;
        if (faxis == X_AXIS) {
            newSpan = (int)width;
        } else {
            newSpan = (int)height;
        }
        if (layoutSpan != newSpan) {
            layoutChanged(faxis);
            layoutChanged(getAxis());
            layoutSpan = newSpan;
        }
        if (!isLayoutValid(faxis)) {
            final int heightAxis = getAxis();
            int oldFlowHeight = (int)((heightAxis == X_AXIS) ? getWidth() : getHeight());
            strategy.layout(this);
            int newFlowHeight = (int)getPreferredSpan(heightAxis);
            if (oldFlowHeight != newFlowHeight) {
                View p = getParent();
                if (p != null) {
                    p.preferenceChanged(this, (heightAxis == X_AXIS), (heightAxis == Y_AXIS));
                }
                Component host = getContainer();
                if (host != null) {
                    host.repaint();
                }
            }
        }
        super.layout(width, height);
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        if (r == null) {
            r = new SizeRequirements();
        }
        float pref = layoutPool.getPreferredSpan(axis);
        float min = layoutPool.getMinimumSpan(axis);
        r.minimum = (int)min;
        r.preferred = Math.max(r.minimum, (int)pref);
        r.maximum = Integer.MAX_VALUE;
        r.alignment = 0.5F;
        return r;
    }
    
    public void insertUpdate(DocumentEvent changes, Shape a, ViewFactory f) {
        layoutPool.insertUpdate(changes, a, f);
        strategy.insertUpdate(this, changes, getInsideAllocation(a));
    }
    
    public void removeUpdate(DocumentEvent changes, Shape a, ViewFactory f) {
        layoutPool.removeUpdate(changes, a, f);
        strategy.removeUpdate(this, changes, getInsideAllocation(a));
    }
    
    public void changedUpdate(DocumentEvent changes, Shape a, ViewFactory f) {
        layoutPool.changedUpdate(changes, a, f);
        strategy.changedUpdate(this, changes, getInsideAllocation(a));
    }
    
    public void setParent(View parent) {
        super.setParent(parent);
        if (parent == null && layoutPool != null) {
            layoutPool.setParent(null);
        }
    }
    protected int layoutSpan;
    protected View layoutPool;
    protected FlowView$FlowStrategy strategy;
    {
    }
    {
    }
}
