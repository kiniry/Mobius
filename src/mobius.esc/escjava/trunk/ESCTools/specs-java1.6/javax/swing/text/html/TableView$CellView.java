package javax.swing.text.html;

import java.awt.*;
import javax.swing.SizeRequirements;
import javax.swing.text.*;

class TableView$CellView extends BlockView {
    /*synthetic*/ final TableView this$0;
    
    public TableView$CellView(/*synthetic*/ final TableView this$0, Element elem) {
        super(elem, Y_AXIS);
        this.this$0 = this$0;
    }
    
    protected void layoutMajorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        super.layoutMajorAxis(targetSpan, axis, offsets, spans);
        int used = 0;
        int n = spans.length;
        for (int i = 0; i < n; i++) {
            used += spans[i];
        }
        int adjust = 0;
        if (used < targetSpan) {
            String valign = (String)(String)getElement().getAttributes().getAttribute(HTML$Attribute.VALIGN);
            if (valign == null) {
                AttributeSet rowAttr = getElement().getParentElement().getAttributes();
                valign = (String)(String)rowAttr.getAttribute(HTML$Attribute.VALIGN);
            }
            if ((valign == null) || valign.equals("middle")) {
                adjust = (targetSpan - used) / 2;
            } else if (valign.equals("bottom")) {
                adjust = targetSpan - used;
            }
        }
        if (adjust != 0) {
            for (int i = 0; i < n; i++) {
                offsets[i] += adjust;
            }
        }
    }
    
    protected SizeRequirements calculateMajorAxisRequirements(int axis, SizeRequirements r) {
        SizeRequirements req = super.calculateMajorAxisRequirements(axis, r);
        req.maximum = Integer.MAX_VALUE;
        return req;
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        SizeRequirements rv = super.calculateMinorAxisRequirements(axis, r);
        int n = getViewCount();
        int min = 0;
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            min = Math.max((int)v.getMinimumSpan(axis), min);
        }
        rv.minimum = Math.min(rv.minimum, min);
        return rv;
    }
}
