package java.sql;

public class SQLException extends java.lang.Exception {
    
    public SQLException(String reason, String SQLState, int vendorCode) {
        super(reason);
        this.SQLState = SQLState;
        this.vendorCode = vendorCode;
        if (!(this instanceof SQLWarning)) {
            if (DriverManager.getLogWriter() != null) {
                DriverManager.println("SQLException: SQLState(" + SQLState + ") vendor code(" + vendorCode + ")");
                printStackTrace(DriverManager.getLogWriter());
            }
        }
    }
    
    public SQLException(String reason, String SQLState) {
        super(reason);
        this.SQLState = SQLState;
        this.vendorCode = 0;
        if (!(this instanceof SQLWarning)) {
            if (DriverManager.getLogWriter() != null) {
                printStackTrace(DriverManager.getLogWriter());
                DriverManager.println("SQLException: SQLState(" + SQLState + ")");
            }
        }
    }
    
    public SQLException(String reason) {
        super(reason);
        this.SQLState = null;
        this.vendorCode = 0;
        if (!(this instanceof SQLWarning)) {
            if (DriverManager.getLogWriter() != null) {
                printStackTrace(DriverManager.getLogWriter());
            }
        }
    }
    
    public SQLException() {
        
        this.SQLState = null;
        this.vendorCode = 0;
        if (!(this instanceof SQLWarning)) {
            if (DriverManager.getLogWriter() != null) {
                printStackTrace(DriverManager.getLogWriter());
            }
        }
    }
    
    public String getSQLState() {
        return (SQLState);
    }
    
    public int getErrorCode() {
        return (vendorCode);
    }
    
    public SQLException getNextException() {
        return (next);
    }
    
    public synchronized void setNextException(SQLException ex) {
        SQLException theEnd = this;
        while (theEnd.next != null) {
            theEnd = theEnd.next;
        }
        theEnd.next = ex;
    }
    private String SQLState;
    private int vendorCode;
    private SQLException next;
}
