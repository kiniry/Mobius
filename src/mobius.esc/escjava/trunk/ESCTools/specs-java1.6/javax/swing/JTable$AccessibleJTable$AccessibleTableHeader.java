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

class JTable$AccessibleJTable$AccessibleTableHeader implements AccessibleTable {
    /*synthetic*/ final JTable$AccessibleJTable this$1;
    private JTableHeader header;
    private TableColumnModel headerModel;
    
    JTable$AccessibleJTable$AccessibleTableHeader(/*synthetic*/ final JTable$AccessibleJTable this$1, JTableHeader header) {
        this.this$1 = this$1;
        
        this.header = header;
        this.headerModel = header.getColumnModel();
    }
    
    public Accessible getAccessibleCaption() {
        return null;
    }
    
    public void setAccessibleCaption(Accessible a) {
    }
    
    public Accessible getAccessibleSummary() {
        return null;
    }
    
    public void setAccessibleSummary(Accessible a) {
    }
    
    public int getAccessibleRowCount() {
        return 1;
    }
    
    public int getAccessibleColumnCount() {
        return headerModel.getColumnCount();
    }
    
    public Accessible getAccessibleAt(int row, int column) {
        TableColumn aColumn = headerModel.getColumn(column);
        TableCellRenderer renderer = aColumn.getHeaderRenderer();
        if (renderer == null) {
            renderer = header.getDefaultRenderer();
        }
        Component component = renderer.getTableCellRendererComponent(header.getTable(), aColumn.getHeaderValue(), false, false, -1, column);
        return new JTable$AccessibleJTable$AccessibleJTableHeaderCell(this$1, row, column, this$1.this$0.getTableHeader(), component);
    }
    
    public int getAccessibleRowExtentAt(int r, int c) {
        return 1;
    }
    
    public int getAccessibleColumnExtentAt(int r, int c) {
        return 1;
    }
    
    public AccessibleTable getAccessibleRowHeader() {
        return null;
    }
    
    public void setAccessibleRowHeader(AccessibleTable table) {
    }
    
    public AccessibleTable getAccessibleColumnHeader() {
        return null;
    }
    
    public void setAccessibleColumnHeader(AccessibleTable table) {
    }
    
    public Accessible getAccessibleRowDescription(int r) {
        return null;
    }
    
    public void setAccessibleRowDescription(int r, Accessible a) {
    }
    
    public Accessible getAccessibleColumnDescription(int c) {
        return null;
    }
    
    public void setAccessibleColumnDescription(int c, Accessible a) {
    }
    
    public boolean isAccessibleSelected(int r, int c) {
        return false;
    }
    
    public boolean isAccessibleRowSelected(int r) {
        return false;
    }
    
    public boolean isAccessibleColumnSelected(int c) {
        return false;
    }
    
    public int[] getSelectedAccessibleRows() {
        return new int[0];
    }
    
    public int[] getSelectedAccessibleColumns() {
        return new int[0];
    }
}
