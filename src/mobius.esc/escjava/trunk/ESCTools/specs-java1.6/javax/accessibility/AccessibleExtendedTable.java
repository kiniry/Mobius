package javax.accessibility;

public interface AccessibleExtendedTable extends AccessibleTable {
    
    public int getAccessibleRow(int index);
    
    public int getAccessibleColumn(int index);
    
    public int getAccessibleIndex(int r, int c);
}
