package javax.swing.text.html;

import java.io.*;
import javax.swing.text.*;

interface CSS$LayoutIterator {
    
    void setOffset(int offs);
    
    int getOffset();
    
    void setSpan(int span);
    
    int getSpan();
    
    int getCount();
    
    void setIndex(int i);
    
    float getMinimumSpan(float parentSpan);
    
    float getPreferredSpan(float parentSpan);
    
    float getMaximumSpan(float parentSpan);
    
    int getAdjustmentWeight();
    
    float getBorderWidth();
    
    float getLeadingCollapseSpan();
    
    float getTrailingCollapseSpan();
    public static final int WorstAdjustmentWeight = 2;
}
