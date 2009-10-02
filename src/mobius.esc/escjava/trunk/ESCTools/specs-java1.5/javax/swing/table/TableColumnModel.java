package javax.swing.table;

import java.util.Enumeration;
import javax.swing.event.*;
import javax.swing.*;

public interface TableColumnModel {
    
    public void addColumn(TableColumn aColumn);
    
    public void removeColumn(TableColumn column);
    
    public void moveColumn(int columnIndex, int newIndex);
    
    public void setColumnMargin(int newMargin);
    
    public int getColumnCount();
    
    public Enumeration getColumns();
    
    public int getColumnIndex(Object columnIdentifier);
    
    public TableColumn getColumn(int columnIndex);
    
    public int getColumnMargin();
    
    public int getColumnIndexAtX(int xPosition);
    
    public int getTotalColumnWidth();
    
    public void setColumnSelectionAllowed(boolean flag);
    
    public boolean getColumnSelectionAllowed();
    
    public int[] getSelectedColumns();
    
    public int getSelectedColumnCount();
    
    public void setSelectionModel(ListSelectionModel newModel);
    
    public ListSelectionModel getSelectionModel();
    
    public void addColumnModelListener(TableColumnModelListener x);
    
    public void removeColumnModelListener(TableColumnModelListener x);
}
