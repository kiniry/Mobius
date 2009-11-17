package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

public class FlowView$FlowStrategy {
    
    public FlowView$FlowStrategy() {
        
    }
    
    public void insertUpdate(FlowView fv, DocumentEvent e, Rectangle alloc) {
        if (alloc != null) {
            Component host = fv.getContainer();
            if (host != null) {
                host.repaint(alloc.x, alloc.y, alloc.width, alloc.height);
            }
        } else {
            fv.preferenceChanged(null, true, true);
        }
    }
    
    public void removeUpdate(FlowView fv, DocumentEvent e, Rectangle alloc) {
        if (alloc != null) {
            Component host = fv.getContainer();
            if (host != null) {
                host.repaint(alloc.x, alloc.y, alloc.width, alloc.height);
            }
        } else {
            fv.preferenceChanged(null, true, true);
        }
    }
    
    public void changedUpdate(FlowView fv, DocumentEvent e, Rectangle alloc) {
        if (alloc != null) {
            Component host = fv.getContainer();
            if (host != null) {
                host.repaint(alloc.x, alloc.y, alloc.width, alloc.height);
            }
        } else {
            fv.preferenceChanged(null, true, true);
        }
    }
    
    protected View getLogicalView(FlowView fv) {
        return fv.layoutPool;
    }
    
    public void layout(FlowView fv) {
        int p0 = fv.getStartOffset();
        int p1 = fv.getEndOffset();
        View lv = getLogicalView(fv);
        int n = lv.getViewCount();
        for (int i = 0; i < n; i++) {
            View v = lv.getView(i);
            v.setParent(lv);
        }
        fv.removeAll();
        for (int rowIndex = 0; p0 < p1; rowIndex++) {
            View row = fv.createRow();
            fv.append(row);
            int next = layoutRow(fv, rowIndex, p0);
            if (row.getViewCount() == 0) {
                row.append(createView(fv, p0, Integer.MAX_VALUE, rowIndex));
                next = row.getEndOffset();
            }
            if (next <= p0) {
                throw new StateInvariantError("infinite loop in formatting");
            } else {
                p0 = next;
            }
        }
    }
    
    protected int layoutRow(FlowView fv, int rowIndex, int pos) {
        View row = fv.getView(rowIndex);
        int x = fv.getFlowStart(rowIndex);
        int spanLeft = fv.getFlowSpan(rowIndex);
        int end = fv.getEndOffset();
        TabExpander te = (fv instanceof TabExpander) ? (TabExpander)(TabExpander)fv : null;
        int preX = x;
        int availableSpan = spanLeft;
        preX = x;
        final int flowAxis = fv.getFlowAxis();
        boolean forcedBreak = false;
        while (pos < end && spanLeft >= 0) {
            View v = createView(fv, pos, spanLeft, rowIndex);
            if ((v == null) || (spanLeft == 0 && v.getPreferredSpan(flowAxis) > 0)) {
                break;
            }
            int chunkSpan;
            if ((flowAxis == 0) && (v instanceof TabableView)) {
                chunkSpan = (int)((TabableView)(TabableView)v).getTabbedSpan(x, te);
            } else {
                chunkSpan = (int)v.getPreferredSpan(flowAxis);
            }
            if (v.getBreakWeight(flowAxis, pos, spanLeft) >= 3000) {
                int n = row.getViewCount();
                if (n > 0) {
                    v = v.breakView(flowAxis, pos, x, spanLeft);
                    if (v != null) {
                        if ((flowAxis == 0) && (v instanceof TabableView)) {
                            chunkSpan = (int)((TabableView)(TabableView)v).getTabbedSpan(x, te);
                        } else {
                            chunkSpan = (int)v.getPreferredSpan(flowAxis);
                        }
                    } else {
                        chunkSpan = 0;
                    }
                }
                forcedBreak = true;
            }
            spanLeft -= chunkSpan;
            x += chunkSpan;
            if (v != null) {
                row.append(v);
                pos = v.getEndOffset();
            }
            if (forcedBreak) {
                break;
            }
        }
        if (spanLeft < 0) {
            adjustRow(fv, rowIndex, availableSpan, preX);
        } else if (row.getViewCount() == 0) {
            View v = createView(fv, pos, Integer.MAX_VALUE, rowIndex);
            row.append(v);
        }
        return row.getEndOffset();
    }
    
    protected void adjustRow(FlowView fv, int rowIndex, int desiredSpan, int x) {
        final int flowAxis = fv.getFlowAxis();
        View r = fv.getView(rowIndex);
        int n = r.getViewCount();
        int span = 0;
        int bestWeight = 0;
        int bestSpan = 0;
        int bestIndex = -1;
        int bestOffset = 0;
        View v;
        for (int i = 0; i < n; i++) {
            v = r.getView(i);
            int spanLeft = desiredSpan - span;
            int w = v.getBreakWeight(flowAxis, x + span, spanLeft);
            if ((w >= bestWeight) && (w > 0)) {
                bestWeight = w;
                bestIndex = i;
                bestSpan = span;
                if (w >= 3000) {
                    break;
                }
            }
            span += v.getPreferredSpan(flowAxis);
        }
        if (bestIndex < 0) {
            return;
        }
        int spanLeft = desiredSpan - bestSpan;
        v = r.getView(bestIndex);
        v = v.breakView(flowAxis, v.getStartOffset(), x + bestSpan, spanLeft);
        View[] va = new View[1];
        va[0] = v;
        View lv = getLogicalView(fv);
        for (int i = bestIndex; i < n; i++) {
            View tmpView = r.getView(i);
            if (contains(lv, tmpView)) {
                tmpView.setParent(lv);
            } else if (tmpView.getViewCount() > 0) {
                recursiveReparent(tmpView, lv);
            }
        }
        r.replace(bestIndex, n - bestIndex, va);
    }
    
    private void recursiveReparent(View v, View logicalView) {
        int n = v.getViewCount();
        for (int i = 0; i < n; i++) {
            View tmpView = v.getView(i);
            if (contains(logicalView, tmpView)) {
                tmpView.setParent(logicalView);
            } else {
                recursiveReparent(tmpView, logicalView);
            }
        }
    }
    
    private boolean contains(View logicalView, View v) {
        int n = logicalView.getViewCount();
        for (int i = 0; i < n; i++) {
            if (logicalView.getView(i) == v) {
                return true;
            }
        }
        return false;
    }
    
    protected View createView(FlowView fv, int startOffset, int spanLeft, int rowIndex) {
        View lv = getLogicalView(fv);
        int childIndex = lv.getViewIndex(startOffset, Position$Bias.Forward);
        View v = lv.getView(childIndex);
        if (startOffset == v.getStartOffset()) {
            return v;
        }
        v = v.createFragment(startOffset, v.getEndOffset());
        return v;
    }
}
