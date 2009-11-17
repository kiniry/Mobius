package javax.swing.text.html;

import java.awt.*;
import javax.swing.text.*;

class TableView$RowIterator implements CSS$LayoutIterator {
    /*synthetic*/ final TableView this$0;
    
    TableView$RowIterator(/*synthetic*/ final TableView this$0) {
        this.this$0 = this$0;
        
    }
    
    void updateAdjustments() {
        int axis = 1;
        if (TableView.access$300(this$0)) {
            int n = this$0.getRowCount();
            adjustments = new int[n];
            for (int i = 0; i < n; i++) {
                TableView$RowView rv = this$0.getRow(i);
                if (rv.multiRowCells == true) {
                    int ncells = rv.getViewCount();
                    for (int j = 0; j < ncells; j++) {
                        View v = rv.getView(j);
                        int nrows = this$0.getRowsOccupied(v);
                        if (nrows > 1) {
                            int spanNeeded = (int)v.getPreferredSpan(axis);
                            adjustMultiRowSpan(spanNeeded, nrows, i);
                        }
                    }
                }
            }
        } else {
            adjustments = null;
        }
    }
    
    void adjustMultiRowSpan(int spanNeeded, int nrows, int rowIndex) {
        if ((rowIndex + nrows) > getCount()) {
            nrows = getCount() - rowIndex;
            if (nrows < 1) {
                return;
            }
        }
        int span = 0;
        for (int i = 0; i < nrows; i++) {
            TableView$RowView rv = this$0.getRow(rowIndex + i);
            span += rv.getPreferredSpan(1);
        }
        if (spanNeeded > span) {
            int adjust = (spanNeeded - span);
            int rowAdjust = adjust / nrows;
            int firstAdjust = rowAdjust + (adjust - (rowAdjust * nrows));
            TableView$RowView rv = this$0.getRow(rowIndex);
            adjustments[rowIndex] = Math.max(adjustments[rowIndex], firstAdjust);
            for (int i = 1; i < nrows; i++) {
                adjustments[rowIndex + i] = Math.max(adjustments[rowIndex + i], rowAdjust);
            }
        }
    }
    
    void setLayoutArrays(int[] offsets, int[] spans) {
        this.offsets = offsets;
        this.spans = spans;
    }
    
    public void setOffset(int offs) {
        TableView$RowView rv = this$0.getRow(row);
        if (rv != null) {
            offsets[rv.viewIndex] = offs;
        }
    }
    
    public int getOffset() {
        TableView$RowView rv = this$0.getRow(row);
        if (rv != null) {
            return offsets[rv.viewIndex];
        }
        return 0;
    }
    
    public void setSpan(int span) {
        TableView$RowView rv = this$0.getRow(row);
        if (rv != null) {
            spans[rv.viewIndex] = span;
        }
    }
    
    public int getSpan() {
        TableView$RowView rv = this$0.getRow(row);
        if (rv != null) {
            return spans[rv.viewIndex];
        }
        return 0;
    }
    
    public int getCount() {
        return this$0.rows.size();
    }
    
    public void setIndex(int i) {
        row = i;
    }
    
    public float getMinimumSpan(float parentSpan) {
        return getPreferredSpan(parentSpan);
    }
    
    public float getPreferredSpan(float parentSpan) {
        TableView$RowView rv = this$0.getRow(row);
        if (rv != null) {
            int adjust = (adjustments != null) ? adjustments[row] : 0;
            return rv.getPreferredSpan(this$0.getAxis()) + adjust;
        }
        return 0;
    }
    
    public float getMaximumSpan(float parentSpan) {
        return getPreferredSpan(parentSpan);
    }
    
    public float getBorderWidth() {
        return TableView.access$100(this$0);
    }
    
    public float getLeadingCollapseSpan() {
        return TableView.access$200(this$0);
    }
    
    public float getTrailingCollapseSpan() {
        return TableView.access$200(this$0);
    }
    
    public int getAdjustmentWeight() {
        return 0;
    }
    private int row;
    private int[] adjustments;
    private int[] offsets;
    private int[] spans;
}
