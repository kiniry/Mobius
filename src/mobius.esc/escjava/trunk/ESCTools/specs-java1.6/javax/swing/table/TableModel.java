package javax.swing.table;

import javax.swing.*;
import javax.swing.event.*;

public interface TableModel {
    
    public int getRowCount();
    
    public int getColumnCount();
    
    public String getColumnName(int columnIndex);
    
    public Class getColumnClass(int columnIndex);
    
    public boolean isCellEditable(int rowIndex, int columnIndex);
    
    public Object getValueAt(int rowIndex, int columnIndex);
    
    public void setValueAt(Object aValue, int rowIndex, int columnIndex);
    
    public void addTableModelListener(TableModelListener l);
    
    public void removeTableModelListener(TableModelListener l);
}
