package javax.swing.table;

import java.io.Serializable;
import java.util.Vector;
import javax.swing.event.TableModelEvent;

public class DefaultTableModel extends AbstractTableModel implements Serializable {
    protected Vector dataVector;
    protected Vector columnIdentifiers;
    
    public DefaultTableModel() {
        this(0, 0);
    }
    
    private static Vector newVector(int size) {
        Vector v = new Vector(size);
        v.setSize(size);
        return v;
    }
    
    public DefaultTableModel(int rowCount, int columnCount) {
        this(newVector(columnCount), rowCount);
    }
    
    public DefaultTableModel(Vector columnNames, int rowCount) {
        
        setDataVector(newVector(rowCount), columnNames);
    }
    
    public DefaultTableModel(Object[] columnNames, int rowCount) {
        this(convertToVector(columnNames), rowCount);
    }
    
    public DefaultTableModel(Vector data, Vector columnNames) {
        
        setDataVector(data, columnNames);
    }
    
    public DefaultTableModel(Object[][] data, Object[] columnNames) {
        
        setDataVector(data, columnNames);
    }
    
    public Vector getDataVector() {
        return dataVector;
    }
    
    private static Vector nonNullVector(Vector v) {
        return (v != null) ? v : new Vector();
    }
    
    public void setDataVector(Vector dataVector, Vector columnIdentifiers) {
        this.dataVector = nonNullVector(dataVector);
        this.columnIdentifiers = nonNullVector(columnIdentifiers);
        justifyRows(0, getRowCount());
        fireTableStructureChanged();
    }
    
    public void setDataVector(Object[][] dataVector, Object[] columnIdentifiers) {
        setDataVector(convertToVector(dataVector), convertToVector(columnIdentifiers));
    }
    
    public void newDataAvailable(TableModelEvent event) {
        fireTableChanged(event);
    }
    
    private void justifyRows(int from, int to) {
        dataVector.setSize(getRowCount());
        for (int i = from; i < to; i++) {
            if (dataVector.elementAt(i) == null) {
                dataVector.setElementAt(new Vector(), i);
            }
            ((Vector)(Vector)dataVector.elementAt(i)).setSize(getColumnCount());
        }
    }
    
    public void newRowsAdded(TableModelEvent e) {
        justifyRows(e.getFirstRow(), e.getLastRow() + 1);
        fireTableChanged(e);
    }
    
    public void rowsRemoved(TableModelEvent event) {
        fireTableChanged(event);
    }
    
    public void setNumRows(int rowCount) {
        int old = getRowCount();
        if (old == rowCount) {
            return;
        }
        dataVector.setSize(rowCount);
        if (rowCount <= old) {
            fireTableRowsDeleted(rowCount, old - 1);
        } else {
            justifyRows(old, rowCount);
            fireTableRowsInserted(old, rowCount - 1);
        }
    }
    
    public void setRowCount(int rowCount) {
        setNumRows(rowCount);
    }
    
    public void addRow(Vector rowData) {
        insertRow(getRowCount(), rowData);
    }
    
    public void addRow(Object[] rowData) {
        addRow(convertToVector(rowData));
    }
    
    public void insertRow(int row, Vector rowData) {
        dataVector.insertElementAt(rowData, row);
        justifyRows(row, row + 1);
        fireTableRowsInserted(row, row);
    }
    
    public void insertRow(int row, Object[] rowData) {
        insertRow(row, convertToVector(rowData));
    }
    
    private static int gcd(int i, int j) {
        return (j == 0) ? i : gcd(j, i % j);
    }
    
    private static void rotate(Vector v, int a, int b, int shift) {
        int size = b - a;
        int r = size - shift;
        int g = gcd(size, r);
        for (int i = 0; i < g; i++) {
            int to = i;
            Object tmp = v.elementAt(a + to);
            for (int from = (to + r) % size; from != i; from = (to + r) % size) {
                v.setElementAt(v.elementAt(a + from), a + to);
                to = from;
            }
            v.setElementAt(tmp, a + to);
        }
    }
    
    public void moveRow(int start, int end, int to) {
        int shift = to - start;
        int first;
        int last;
        if (shift < 0) {
            first = to;
            last = end;
        } else {
            first = start;
            last = to + end - start;
        }
        rotate(dataVector, first, last + 1, shift);
        fireTableRowsUpdated(first, last);
    }
    
    public void removeRow(int row) {
        dataVector.removeElementAt(row);
        fireTableRowsDeleted(row, row);
    }
    
    public void setColumnIdentifiers(Vector columnIdentifiers) {
        setDataVector(dataVector, columnIdentifiers);
    }
    
    public void setColumnIdentifiers(Object[] newIdentifiers) {
        setColumnIdentifiers(convertToVector(newIdentifiers));
    }
    
    public void setColumnCount(int columnCount) {
        columnIdentifiers.setSize(columnCount);
        justifyRows(0, getRowCount());
        fireTableStructureChanged();
    }
    
    public void addColumn(Object columnName) {
        addColumn(columnName, (Vector)null);
    }
    
    public void addColumn(Object columnName, Vector columnData) {
        columnIdentifiers.addElement(columnName);
        if (columnData != null) {
            int columnSize = columnData.size();
            if (columnSize > getRowCount()) {
                dataVector.setSize(columnSize);
            }
            justifyRows(0, getRowCount());
            int newColumn = getColumnCount() - 1;
            for (int i = 0; i < columnSize; i++) {
                Vector row = (Vector)(Vector)dataVector.elementAt(i);
                row.setElementAt(columnData.elementAt(i), newColumn);
            }
        } else {
            justifyRows(0, getRowCount());
        }
        fireTableStructureChanged();
    }
    
    public void addColumn(Object columnName, Object[] columnData) {
        addColumn(columnName, convertToVector(columnData));
    }
    
    public int getRowCount() {
        return dataVector.size();
    }
    
    public int getColumnCount() {
        return columnIdentifiers.size();
    }
    
    public String getColumnName(int column) {
        Object id = null;
        if (column < columnIdentifiers.size()) {
            id = columnIdentifiers.elementAt(column);
        }
        return (id == null) ? super.getColumnName(column) : id.toString();
    }
    
    public boolean isCellEditable(int row, int column) {
        return true;
    }
    
    public Object getValueAt(int row, int column) {
        Vector rowVector = (Vector)(Vector)dataVector.elementAt(row);
        return rowVector.elementAt(column);
    }
    
    public void setValueAt(Object aValue, int row, int column) {
        Vector rowVector = (Vector)(Vector)dataVector.elementAt(row);
        rowVector.setElementAt(aValue, column);
        fireTableCellUpdated(row, column);
    }
    
    protected static Vector convertToVector(Object[] anArray) {
        if (anArray == null) {
            return null;
        }
        Vector v = new Vector(anArray.length);
        for (int i = 0; i < anArray.length; i++) {
            v.addElement(anArray[i]);
        }
        return v;
    }
    
    protected static Vector convertToVector(Object[][] anArray) {
        if (anArray == null) {
            return null;
        }
        Vector v = new Vector(anArray.length);
        for (int i = 0; i < anArray.length; i++) {
            v.addElement(convertToVector(anArray[i]));
        }
        return v;
    }
}
