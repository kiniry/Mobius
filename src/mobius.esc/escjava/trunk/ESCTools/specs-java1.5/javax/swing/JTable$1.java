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

class JTable$1 extends AbstractTableModel {
    /*synthetic*/ final Object[][] val$rowData;
    /*synthetic*/ final Object[] val$columnNames;
    
    JTable$1(/*synthetic*/ final Object[] val$columnNames, /*synthetic*/ final Object[][] val$rowData) {
        this.val$columnNames = val$columnNames;
        this.val$rowData = val$rowData;
        
    }
    
    public String getColumnName(int column) {
        return val$columnNames[column].toString();
    }
    
    public int getRowCount() {
        return val$rowData.length;
    }
    
    public int getColumnCount() {
        return val$columnNames.length;
    }
    
    public Object getValueAt(int row, int col) {
        return val$rowData[row][col];
    }
    
    public boolean isCellEditable(int row, int column) {
        return true;
    }
    
    public void setValueAt(Object value, int row, int col) {
        val$rowData[row][col] = value;
        fireTableCellUpdated(row, col);
    }
}
