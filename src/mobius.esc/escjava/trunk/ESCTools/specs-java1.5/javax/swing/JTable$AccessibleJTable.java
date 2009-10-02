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

public class JTable$AccessibleJTable extends JComponent$AccessibleJComponent implements AccessibleSelection, ListSelectionListener, TableModelListener, TableColumnModelListener, CellEditorListener, PropertyChangeListener, AccessibleExtendedTable {
    /*synthetic*/ final JTable this$0;
    int lastSelectedRow;
    int lastSelectedCol;
    
    protected JTable$AccessibleJTable(/*synthetic*/ final JTable this$0) {
        this.this$0 = this$0;
        super(this$0);
        this$0.addPropertyChangeListener(this);
        this$0.getSelectionModel().addListSelectionListener(this);
        TableColumnModel tcm = this$0.getColumnModel();
        tcm.addColumnModelListener(this);
        tcm.getSelectionModel().addListSelectionListener(this);
        this$0.getModel().addTableModelListener(this);
        lastSelectedRow = this$0.getSelectedRow();
        lastSelectedCol = this$0.getSelectedColumn();
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String name = e.getPropertyName();
        Object oldValue = e.getOldValue();
        Object newValue = e.getNewValue();
        if (name.compareTo("model") == 0) {
            if (oldValue != null && oldValue instanceof TableModel) {
                ((TableModel)(TableModel)oldValue).removeTableModelListener(this);
            }
            if (newValue != null && newValue instanceof TableModel) {
                ((TableModel)(TableModel)newValue).addTableModelListener(this);
            }
        } else if (name.compareTo("selectionModel") == 0) {
            Object source = e.getSource();
            if (source == this$0) {
                if (oldValue != null && oldValue instanceof ListSelectionModel) {
                    ((ListSelectionModel)(ListSelectionModel)oldValue).removeListSelectionListener(this);
                }
                if (newValue != null && newValue instanceof ListSelectionModel) {
                    ((ListSelectionModel)(ListSelectionModel)newValue).addListSelectionListener(this);
                }
            } else if (source == this$0.getColumnModel()) {
                if (oldValue != null && oldValue instanceof ListSelectionModel) {
                    ((ListSelectionModel)(ListSelectionModel)oldValue).removeListSelectionListener(this);
                }
                if (newValue != null && newValue instanceof ListSelectionModel) {
                    ((ListSelectionModel)(ListSelectionModel)newValue).addListSelectionListener(this);
                }
            } else {
            }
        } else if (name.compareTo("columnModel") == 0) {
            if (oldValue != null && oldValue instanceof TableColumnModel) {
                TableColumnModel tcm = (TableColumnModel)(TableColumnModel)oldValue;
                tcm.removeColumnModelListener(this);
                tcm.getSelectionModel().removeListSelectionListener(this);
            }
            if (newValue != null && newValue instanceof TableColumnModel) {
                TableColumnModel tcm = (TableColumnModel)(TableColumnModel)newValue;
                tcm.addColumnModelListener(this);
                tcm.getSelectionModel().addListSelectionListener(this);
            }
        } else if (name.compareTo("tableCellEditor") == 0) {
            if (oldValue != null && oldValue instanceof TableCellEditor) {
                ((TableCellEditor)(TableCellEditor)oldValue).removeCellEditorListener((CellEditorListener)this);
            }
            if (newValue != null && newValue instanceof TableCellEditor) {
                ((TableCellEditor)(TableCellEditor)newValue).addCellEditorListener((CellEditorListener)this);
            }
        }
    }
    {
    }
    
    public void tableChanged(TableModelEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, null);
        if (e != null) {
            int firstColumn = e.getColumn();
            int lastColumn = e.getColumn();
            if (firstColumn == TableModelEvent.ALL_COLUMNS) {
                firstColumn = 0;
                lastColumn = this$0.getColumnCount() - 1;
            }
            JTable$AccessibleJTable$AccessibleJTableModelChange change = new JTable$AccessibleJTable$AccessibleJTableModelChange(this, e.getType(), e.getFirstRow(), e.getLastRow(), firstColumn, lastColumn);
            firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_MODEL_CHANGED, null, change);
        }
    }
    
    public void tableRowsInserted(TableModelEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, null);
        int firstColumn = e.getColumn();
        int lastColumn = e.getColumn();
        if (firstColumn == TableModelEvent.ALL_COLUMNS) {
            firstColumn = 0;
            lastColumn = this$0.getColumnCount() - 1;
        }
        JTable$AccessibleJTable$AccessibleJTableModelChange change = new JTable$AccessibleJTable$AccessibleJTableModelChange(this, e.getType(), e.getFirstRow(), e.getLastRow(), firstColumn, lastColumn);
        firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_MODEL_CHANGED, null, change);
    }
    
    public void tableRowsDeleted(TableModelEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, null);
        int firstColumn = e.getColumn();
        int lastColumn = e.getColumn();
        if (firstColumn == TableModelEvent.ALL_COLUMNS) {
            firstColumn = 0;
            lastColumn = this$0.getColumnCount() - 1;
        }
        JTable$AccessibleJTable$AccessibleJTableModelChange change = new JTable$AccessibleJTable$AccessibleJTableModelChange(this, e.getType(), e.getFirstRow(), e.getLastRow(), firstColumn, lastColumn);
        firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_MODEL_CHANGED, null, change);
    }
    
    public void columnAdded(TableColumnModelEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, null);
        int type = AccessibleTableModelChange.INSERT;
        JTable$AccessibleJTable$AccessibleJTableModelChange change = new JTable$AccessibleJTable$AccessibleJTableModelChange(this, type, 0, 0, e.getFromIndex(), e.getToIndex());
        firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_MODEL_CHANGED, null, change);
    }
    
    public void columnRemoved(TableColumnModelEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, null);
        int type = AccessibleTableModelChange.DELETE;
        JTable$AccessibleJTable$AccessibleJTableModelChange change = new JTable$AccessibleJTable$AccessibleJTableModelChange(this, type, 0, 0, e.getFromIndex(), e.getToIndex());
        firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_MODEL_CHANGED, null, change);
    }
    
    public void columnMoved(TableColumnModelEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, null);
        int type = AccessibleTableModelChange.DELETE;
        JTable$AccessibleJTable$AccessibleJTableModelChange change = new JTable$AccessibleJTable$AccessibleJTableModelChange(this, type, 0, 0, e.getFromIndex(), e.getFromIndex());
        firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_MODEL_CHANGED, null, change);
        int type2 = AccessibleTableModelChange.INSERT;
        JTable$AccessibleJTable$AccessibleJTableModelChange change2 = new JTable$AccessibleJTable$AccessibleJTableModelChange(this, type2, 0, 0, e.getToIndex(), e.getToIndex());
        firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_MODEL_CHANGED, null, change2);
    }
    
    public void columnMarginChanged(ChangeEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, null);
    }
    
    public void columnSelectionChanged(ListSelectionEvent e) {
    }
    
    public void editingStopped(ChangeEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, null);
    }
    
    public void editingCanceled(ChangeEvent e) {
    }
    
    public void valueChanged(ListSelectionEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_SELECTION_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
        int selectedRow = this$0.getSelectedRow();
        int selectedCol = this$0.getSelectedColumn();
        if (selectedRow != lastSelectedRow || selectedCol != lastSelectedCol) {
            Accessible oldA = getAccessibleAt(lastSelectedRow, lastSelectedCol);
            Accessible newA = getAccessibleAt(selectedRow, selectedCol);
            firePropertyChange(AccessibleContext.ACCESSIBLE_ACTIVE_DESCENDANT_PROPERTY, oldA, newA);
            lastSelectedRow = selectedRow;
            lastSelectedCol = selectedCol;
        }
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TABLE;
    }
    
    public Accessible getAccessibleAt(Point p) {
        int column = this$0.columnAtPoint(p);
        int row = this$0.rowAtPoint(p);
        if ((column != -1) && (row != -1)) {
            TableColumn aColumn = this$0.getColumnModel().getColumn(column);
            TableCellRenderer renderer = aColumn.getCellRenderer();
            if (renderer == null) {
                Class columnClass = this$0.getColumnClass(column);
                renderer = this$0.getDefaultRenderer(columnClass);
            }
            Component component = renderer.getTableCellRendererComponent(this$0, null, false, false, row, column);
            return new JTable$AccessibleJTable$AccessibleJTableCell(this, this$0, row, column, getAccessibleIndexAt(row, column));
        }
        return null;
    }
    
    public int getAccessibleChildrenCount() {
        return (this$0.getColumnCount() * this$0.getRowCount());
    }
    
    public Accessible getAccessibleChild(int i) {
        if (i < 0 || i >= getAccessibleChildrenCount()) {
            return null;
        } else {
            int column = getAccessibleColumnAtIndex(i);
            int row = getAccessibleRowAtIndex(i);
            TableColumn aColumn = this$0.getColumnModel().getColumn(column);
            TableCellRenderer renderer = aColumn.getCellRenderer();
            if (renderer == null) {
                Class columnClass = this$0.getColumnClass(column);
                renderer = this$0.getDefaultRenderer(columnClass);
            }
            Component component = renderer.getTableCellRendererComponent(this$0, null, false, false, row, column);
            return new JTable$AccessibleJTable$AccessibleJTableCell(this, this$0, row, column, getAccessibleIndexAt(row, column));
        }
    }
    
    public int getAccessibleSelectionCount() {
        int rowsSel = this$0.getSelectedRowCount();
        int colsSel = this$0.getSelectedColumnCount();
        if (this$0.cellSelectionEnabled) {
            return rowsSel * colsSel;
        } else {
            if (this$0.getRowSelectionAllowed() && this$0.getColumnSelectionAllowed()) {
                return rowsSel * this$0.getColumnCount() + colsSel * this$0.getRowCount() - rowsSel * colsSel;
            } else if (this$0.getRowSelectionAllowed()) {
                return rowsSel * this$0.getColumnCount();
            } else if (this$0.getColumnSelectionAllowed()) {
                return colsSel * this$0.getRowCount();
            } else {
                return 0;
            }
        }
    }
    
    public Accessible getAccessibleSelection(int i) {
        if (i < 0 || i > getAccessibleSelectionCount()) {
            return (Accessible)null;
        }
        int rowsSel = this$0.getSelectedRowCount();
        int colsSel = this$0.getSelectedColumnCount();
        int[] rowIndicies = this$0.getSelectedRows();
        int[] colIndicies = this$0.getSelectedColumns();
        int ttlCols = this$0.getColumnCount();
        int ttlRows = this$0.getRowCount();
        int r;
        int c;
        if (this$0.cellSelectionEnabled) {
            r = rowIndicies[i / colsSel];
            c = colIndicies[i % colsSel];
            return getAccessibleChild((r * ttlCols) + c);
        } else {
            if (this$0.getRowSelectionAllowed() && this$0.getColumnSelectionAllowed()) {
                int curIndex = i;
                final int IN_ROW = 0;
                final int NOT_IN_ROW = 1;
                int state = (rowIndicies[0] == 0 ? IN_ROW : NOT_IN_ROW);
                int j = 0;
                int prevRow = -1;
                while (j < rowIndicies.length) {
                    switch (state) {
                    case IN_ROW: 
                        if (curIndex < ttlCols) {
                            c = curIndex % ttlCols;
                            r = rowIndicies[j];
                            return getAccessibleChild((r * ttlCols) + c);
                        } else {
                            curIndex -= ttlCols;
                        }
                        if (j + 1 == rowIndicies.length || rowIndicies[j] != rowIndicies[j + 1] - 1) {
                            state = NOT_IN_ROW;
                            prevRow = rowIndicies[j];
                        }
                        j++;
                        break;
                    
                    case NOT_IN_ROW: 
                        if (curIndex < (colsSel * (rowIndicies[j] - (prevRow == -1 ? 0 : (prevRow + 1))))) {
                            c = colIndicies[curIndex % colsSel];
                            r = (j > 0 ? rowIndicies[j - 1] + 1 : 0) + curIndex / colsSel;
                            return getAccessibleChild((r * ttlCols) + c);
                        } else {
                            curIndex -= colsSel * (rowIndicies[j] - (prevRow == -1 ? 0 : (prevRow + 1)));
                        }
                        state = IN_ROW;
                        break;
                    
                    }
                }
                if (curIndex < (colsSel * (ttlRows - (prevRow == -1 ? 0 : (prevRow + 1))))) {
                    c = colIndicies[curIndex % colsSel];
                    r = rowIndicies[j - 1] + curIndex / colsSel + 1;
                    return getAccessibleChild((r * ttlCols) + c);
                } else {
                }
            } else if (this$0.getRowSelectionAllowed()) {
                c = i % ttlCols;
                r = rowIndicies[i / ttlCols];
                return getAccessibleChild((r * ttlCols) + c);
            } else if (this$0.getColumnSelectionAllowed()) {
                c = colIndicies[i % colsSel];
                r = i / colsSel;
                return getAccessibleChild((r * ttlCols) + c);
            }
        }
        return (Accessible)null;
    }
    
    public boolean isAccessibleChildSelected(int i) {
        int column = getAccessibleColumnAtIndex(i);
        int row = getAccessibleRowAtIndex(i);
        return this$0.isCellSelected(row, column);
    }
    
    public void addAccessibleSelection(int i) {
        int column = getAccessibleColumnAtIndex(i);
        int row = getAccessibleRowAtIndex(i);
        this$0.changeSelection(row, column, true, false);
    }
    
    public void removeAccessibleSelection(int i) {
        if (this$0.cellSelectionEnabled) {
            int column = getAccessibleColumnAtIndex(i);
            int row = getAccessibleRowAtIndex(i);
            this$0.removeRowSelectionInterval(row, row);
            this$0.removeColumnSelectionInterval(column, column);
        }
    }
    
    public void clearAccessibleSelection() {
        this$0.clearSelection();
    }
    
    public void selectAllAccessibleSelection() {
        if (this$0.cellSelectionEnabled) {
            this$0.selectAll();
        }
    }
    
    public int getAccessibleRow(int index) {
        return getAccessibleRowAtIndex(index);
    }
    
    public int getAccessibleColumn(int index) {
        return getAccessibleColumnAtIndex(index);
    }
    
    public int getAccessibleIndex(int r, int c) {
        return getAccessibleIndexAt(r, c);
    }
    private Accessible caption;
    private Accessible summary;
    private Accessible[] rowDescription;
    private Accessible[] columnDescription;
    
    public AccessibleTable getAccessibleTable() {
        return this;
    }
    
    public Accessible getAccessibleCaption() {
        return this.caption;
    }
    
    public void setAccessibleCaption(Accessible a) {
        Accessible oldCaption = caption;
        this.caption = a;
        firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_CAPTION_CHANGED, oldCaption, this.caption);
    }
    
    public Accessible getAccessibleSummary() {
        return this.summary;
    }
    
    public void setAccessibleSummary(Accessible a) {
        Accessible oldSummary = summary;
        this.summary = a;
        firePropertyChange(AccessibleContext.ACCESSIBLE_TABLE_SUMMARY_CHANGED, oldSummary, this.summary);
    }
    
    public int getAccessibleRowCount() {
        return this$0.getRowCount();
    }
    
    public int getAccessibleColumnCount() {
        return this$0.getColumnCount();
    }
    
    public Accessible getAccessibleAt(int r, int c) {
        return getAccessibleChild((r * getAccessibleColumnCount()) + c);
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
    
    public void setAccessibleRowHeader(AccessibleTable a) {
    }
    
    public AccessibleTable getAccessibleColumnHeader() {
        JTableHeader header = this$0.getTableHeader();
        return header == null ? null : new JTable$AccessibleJTable$AccessibleTableHeader(this, header);
    }
    {
    }
    
    public void setAccessibleColumnHeader(AccessibleTable a) {
    }
    
    public Accessible getAccessibleRowDescription(int r) {
        if (r < 0 || r >= getAccessibleRowCount()) {
            throw new IllegalArgumentException(new Integer(r).toString());
        }
        if (rowDescription == null) {
            return null;
        } else {
            return rowDescription[r];
        }
    }
    
    public void setAccessibleRowDescription(int r, Accessible a) {
        if (r < 0 || r >= getAccessibleRowCount()) {
            throw new IllegalArgumentException(new Integer(r).toString());
        }
        if (rowDescription == null) {
            int numRows = getAccessibleRowCount();
            rowDescription = new Accessible[numRows];
        }
        rowDescription[r] = a;
    }
    
    public Accessible getAccessibleColumnDescription(int c) {
        if (c < 0 || c >= getAccessibleColumnCount()) {
            throw new IllegalArgumentException(new Integer(c).toString());
        }
        if (columnDescription == null) {
            return null;
        } else {
            return columnDescription[c];
        }
    }
    
    public void setAccessibleColumnDescription(int c, Accessible a) {
        if (c < 0 || c >= getAccessibleColumnCount()) {
            throw new IllegalArgumentException(new Integer(c).toString());
        }
        if (columnDescription == null) {
            int numColumns = getAccessibleColumnCount();
            columnDescription = new Accessible[numColumns];
        }
        columnDescription[c] = a;
    }
    
    public boolean isAccessibleSelected(int r, int c) {
        return this$0.isCellSelected(r, c);
    }
    
    public boolean isAccessibleRowSelected(int r) {
        return this$0.isRowSelected(r);
    }
    
    public boolean isAccessibleColumnSelected(int c) {
        return this$0.isColumnSelected(c);
    }
    
    public int[] getSelectedAccessibleRows() {
        return this$0.getSelectedRows();
    }
    
    public int[] getSelectedAccessibleColumns() {
        return this$0.getSelectedColumns();
    }
    
    public int getAccessibleRowAtIndex(int i) {
        int columnCount = getAccessibleColumnCount();
        if (columnCount == 0) {
            return -1;
        } else {
            return (i / columnCount);
        }
    }
    
    public int getAccessibleColumnAtIndex(int i) {
        int columnCount = getAccessibleColumnCount();
        if (columnCount == 0) {
            return -1;
        } else {
            return (i % columnCount);
        }
    }
    
    public int getAccessibleIndexAt(int r, int c) {
        return ((r * getAccessibleColumnCount()) + c);
    }
    {
    }
    {
    }
}
