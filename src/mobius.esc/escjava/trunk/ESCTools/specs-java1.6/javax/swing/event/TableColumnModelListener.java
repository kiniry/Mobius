package javax.swing.event;

import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ChangeEvent;

public interface TableColumnModelListener extends java.util.EventListener {
    
    public void columnAdded(TableColumnModelEvent e);
    
    public void columnRemoved(TableColumnModelEvent e);
    
    public void columnMoved(TableColumnModelEvent e);
    
    public void columnMarginChanged(ChangeEvent e);
    
    public void columnSelectionChanged(ListSelectionEvent e);
}
