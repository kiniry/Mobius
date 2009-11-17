package javax.swing.text.html;

import java.awt.*;
import javax.swing.text.*;

class TableView$ColumnIterator implements CSS$LayoutIterator {
    /*synthetic*/ final TableView this$0;
    
    TableView$ColumnIterator(/*synthetic*/ final TableView this$0) {
        this.this$0 = this$0;
        
    }
    
    void disablePercentages() {
        percentages = null;
    }
    
    private void updatePercentagesAndAdjustmentWeights(int span) {
        adjustmentWeights = new int[this$0.columnRequirements.length];
        for (int i = 0; i < this$0.columnRequirements.length; i++) {
            adjustmentWeights[i] = 0;
        }
        if (TableView.access$000(this$0)) {
            percentages = new int[this$0.columnRequirements.length];
        } else {
            percentages = null;
        }
        int nrows = this$0.getRowCount();
        for (int rowIndex = 0; rowIndex < nrows; rowIndex++) {
            TableView$RowView row = this$0.getRow(rowIndex);
            int col = 0;
            int ncells = row.getViewCount();
            for (int cell = 0; cell < ncells; cell++, col++) {
                View cv = row.getView(cell);
                for (; row.isFilled(col); col++) ;
                int rowSpan = this$0.getRowsOccupied(cv);
                int colSpan = this$0.getColumnsOccupied(cv);
                AttributeSet a = cv.getAttributes();
                CSS$LengthValue lv = (CSS$LengthValue)(CSS$LengthValue)a.getAttribute(CSS$Attribute.WIDTH);
                if (lv != null) {
                    int len = (int)(lv.getValue(span) / colSpan + 0.5F);
                    for (int i = 0; i < colSpan; i++) {
                        if (lv.isPercentage()) {
                            percentages[col + i] = Math.max(percentages[col + i], len);
                            adjustmentWeights[col + i] = Math.max(adjustmentWeights[col + i], WorstAdjustmentWeight);
                        } else {
                            adjustmentWeights[col + i] = Math.max(adjustmentWeights[col + i], WorstAdjustmentWeight - 1);
                        }
                    }
                }
                col += colSpan - 1;
            }
        }
    }
    
    public void setLayoutArrays(int[] offsets, int[] spans, int targetSpan) {
        this.offsets = offsets;
        this.spans = spans;
        updatePercentagesAndAdjustmentWeights(targetSpan);
    }
    
    public int getCount() {
        return this$0.columnRequirements.length;
    }
    
    public void setIndex(int i) {
        col = i;
    }
    
    public void setOffset(int offs) {
        offsets[col] = offs;
    }
    
    public int getOffset() {
        return offsets[col];
    }
    
    public void setSpan(int span) {
        spans[col] = span;
    }
    
    public int getSpan() {
        return spans[col];
    }
    
    public float getMinimumSpan(float parentSpan) {
        return this$0.columnRequirements[col].minimum;
    }
    
    public float getPreferredSpan(float parentSpan) {
        if ((percentages != null) && (percentages[col] != 0)) {
            return Math.max(percentages[col], this$0.columnRequirements[col].minimum);
        }
        return this$0.columnRequirements[col].preferred;
    }
    
    public float getMaximumSpan(float parentSpan) {
        return this$0.columnRequirements[col].maximum;
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
        return adjustmentWeights[col];
    }
    private int col;
    private int[] percentages;
    private int[] adjustmentWeights;
    private int[] offsets;
    private int[] spans;
}
