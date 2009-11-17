package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.print.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.table.*;
import javax.swing.border.*;
import javax.print.attribute.*;

public class JTable$AccessibleJTable$AccessibleJTableModelChange implements AccessibleTableModelChange {
    /*synthetic*/ final JTable$AccessibleJTable this$1;
    protected int type;
    protected int firstRow;
    protected int lastRow;
    protected int firstColumn;
    protected int lastColumn;
    
    protected JTable$AccessibleJTable$AccessibleJTableModelChange(/*synthetic*/ final JTable$AccessibleJTable this$1, int type, int firstRow, int lastRow, int firstColumn, int lastColumn) {
        this.this$1 = this$1;
        
        this.type = type;
        this.firstRow = firstRow;
        this.lastRow = lastRow;
        this.firstColumn = firstColumn;
        this.lastColumn = lastColumn;
    }
    
    public int getType() {
        return type;
    }
    
    public int getFirstRow() {
        return firstRow;
    }
    
    public int getLastRow() {
        return lastRow;
    }
    
    public int getFirstColumn() {
        return firstColumn;
    }
    
    public int getLastColumn() {
        return lastColumn;
    }
}
