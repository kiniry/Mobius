package javax.swing.text.html;

import java.awt.*;
import java.util.BitSet;
import javax.swing.SizeRequirements;
import javax.swing.event.DocumentEvent;
import javax.swing.text.*;

public class TableView$RowView extends BoxView {
    /*synthetic*/ final TableView this$0;
    
    public TableView$RowView(/*synthetic*/ final TableView this$0, Element elem) {
        super(elem, View.X_AXIS);
        this.this$0 = this$0;
        fillColumns = new BitSet();
        this.setPropertiesFromAttributes();
    }
    
    void clearFilledColumns() {
        fillColumns.and(TableView.access$400());
    }
    
    void fillColumn(int col) {
        fillColumns.set(col);
    }
    
    boolean isFilled(int col) {
        return fillColumns.get(col);
    }
    
    int getColumnCount() {
        int nfill = 0;
        int n = fillColumns.size();
        for (int i = 0; i < n; i++) {
            if (fillColumns.get(i)) {
                nfill++;
            }
        }
        return getViewCount() + nfill;
    }
    
    public AttributeSet getAttributes() {
        return attr;
    }
    
    View findViewAtPoint(int x, int y, Rectangle alloc) {
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            if (getChildAllocation(i, alloc).contains(x, y)) {
                childAllocation(i, alloc);
                return getView(i);
            }
        }
        return null;
    }
    
    protected StyleSheet getStyleSheet() {
        HTMLDocument doc = (HTMLDocument)(HTMLDocument)getDocument();
        return doc.getStyleSheet();
    }
    
    public void preferenceChanged(View child, boolean width, boolean height) {
        super.preferenceChanged(child, width, height);
        if (TableView.access$300(this$0) && height) {
            for (int i = rowIndex - 1; i >= 0; i--) {
                TableView$RowView rv = this$0.getRow(i);
                if (rv.multiRowCells) {
                    rv.preferenceChanged(null, false, true);
                    break;
                }
            }
        }
    }
    
    protected SizeRequirements calculateMajorAxisRequirements(int axis, SizeRequirements r) {
        SizeRequirements req = new SizeRequirements();
        req.minimum = this$0.totalColumnRequirements.minimum;
        req.maximum = this$0.totalColumnRequirements.maximum;
        req.preferred = this$0.totalColumnRequirements.preferred;
        req.alignment = 0.0F;
        return req;
    }
    
    public float getMinimumSpan(int axis) {
        float value;
        if (axis == View.X_AXIS) {
            value = this$0.totalColumnRequirements.minimum + getLeftInset() + getRightInset();
        } else {
            value = super.getMinimumSpan(axis);
        }
        return value;
    }
    
    public float getMaximumSpan(int axis) {
        float value;
        if (axis == View.X_AXIS) {
            value = (float)Integer.MAX_VALUE;
        } else {
            value = super.getMaximumSpan(axis);
        }
        return value;
    }
    
    public float getPreferredSpan(int axis) {
        float value;
        if (axis == View.X_AXIS) {
            value = this$0.totalColumnRequirements.preferred + getLeftInset() + getRightInset();
        } else {
            value = super.getPreferredSpan(axis);
        }
        return value;
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        super.changedUpdate(e, a, f);
        int pos = e.getOffset();
        if (pos <= getStartOffset() && (pos + e.getLength()) >= getEndOffset()) {
            this.setPropertiesFromAttributes();
        }
    }
    
    public void paint(Graphics g, Shape allocation) {
        Rectangle a = (Rectangle)(Rectangle)allocation;
        painter.paint(g, a.x, a.y, a.width, a.height, this);
        super.paint(g, a);
    }
    
    public void replace(int offset, int length, View[] views) {
        super.replace(offset, length, views);
        this$0.invalidateGrid();
    }
    
    protected SizeRequirements calculateMinorAxisRequirements(int axis, SizeRequirements r) {
        long min = 0;
        long pref = 0;
        long max = 0;
        multiRowCells = false;
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            if (this$0.getRowsOccupied(v) > 1) {
                multiRowCells = true;
                max = Math.max((int)v.getMaximumSpan(axis), max);
            } else {
                min = Math.max((int)v.getMinimumSpan(axis), min);
                pref = Math.max((int)v.getPreferredSpan(axis), pref);
                max = Math.max((int)v.getMaximumSpan(axis), max);
            }
        }
        if (r == null) {
            r = new SizeRequirements();
            r.alignment = 0.5F;
        }
        r.preferred = (int)pref;
        r.minimum = (int)min;
        r.maximum = (int)max;
        return r;
    }
    
    protected void layoutMajorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        int col = 0;
        int ncells = getViewCount();
        for (int cell = 0; cell < ncells; cell++) {
            View cv = getView(cell);
            if (this$0.skipComments && !(cv instanceof TableView$CellView)) {
                continue;
            }
            for (; isFilled(col); col++) ;
            int colSpan = this$0.getColumnsOccupied(cv);
            spans[cell] = this$0.columnSpans[col];
            offsets[cell] = this$0.columnOffsets[col];
            if (colSpan > 1) {
                int n = this$0.columnSpans.length;
                for (int j = 1; j < colSpan; j++) {
                    if ((col + j) < n) {
                        spans[cell] += this$0.columnSpans[col + j];
                        spans[cell] += TableView.access$200(this$0);
                    }
                }
                col += colSpan - 1;
            }
            col++;
        }
    }
    
    protected void layoutMinorAxis(int targetSpan, int axis, int[] offsets, int[] spans) {
        super.layoutMinorAxis(targetSpan, axis, offsets, spans);
        int col = 0;
        int ncells = getViewCount();
        for (int cell = 0; cell < ncells; cell++, col++) {
            View cv = getView(cell);
            for (; isFilled(col); col++) ;
            int colSpan = this$0.getColumnsOccupied(cv);
            int rowSpan = this$0.getRowsOccupied(cv);
            if (rowSpan > 1) {
                int row0 = rowIndex;
                int row1 = Math.min(rowIndex + rowSpan - 1, this$0.getRowCount() - 1);
                spans[cell] = this$0.getMultiRowSpan(row0, row1);
            }
            if (colSpan > 1) {
                col += colSpan - 1;
            }
        }
    }
    
    public int getResizeWeight(int axis) {
        return 1;
    }
    
    protected View getViewAtPosition(int pos, Rectangle a) {
        int n = getViewCount();
        for (int i = 0; i < n; i++) {
            View v = getView(i);
            int p0 = v.getStartOffset();
            int p1 = v.getEndOffset();
            if ((pos >= p0) && (pos < p1)) {
                if (a != null) {
                    childAllocation(i, a);
                }
                return v;
            }
        }
        if (pos == getEndOffset()) {
            View v = getView(n - 1);
            if (a != null) {
                this.childAllocation(n - 1, a);
            }
            return v;
        }
        return null;
    }
    
    void setPropertiesFromAttributes() {
        StyleSheet sheet = getStyleSheet();
        attr = sheet.getViewAttributes(this);
        painter = sheet.getBoxPainter(attr);
    }
    private StyleSheet$BoxPainter painter;
    private AttributeSet attr;
    BitSet fillColumns;
    int rowIndex;
    int viewIndex;
    boolean multiRowCells;
}
