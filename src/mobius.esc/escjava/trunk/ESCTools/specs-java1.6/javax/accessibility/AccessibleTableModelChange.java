package javax.accessibility;

public interface AccessibleTableModelChange {
    public static final int INSERT = 1;
    public static final int UPDATE = 0;
    public static final int DELETE = -1;
    
    public int getType();
    
    public int getFirstRow();
    
    public int getLastRow();
    
    public int getFirstColumn();
    
    public int getLastColumn();
}
