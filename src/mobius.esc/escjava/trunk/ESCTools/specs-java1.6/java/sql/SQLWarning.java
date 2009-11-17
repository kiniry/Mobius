package java.sql;

public class SQLWarning extends SQLException {
    
    public SQLWarning(String reason, String SQLstate, int vendorCode) {
        super(reason, SQLstate, vendorCode);
        DriverManager.println("SQLWarning: reason(" + reason + ") SQLstate(" + SQLstate + ") vendor code(" + vendorCode + ")");
    }
    
    public SQLWarning(String reason, String SQLstate) {
        super(reason, SQLstate);
        DriverManager.println("SQLWarning: reason(" + reason + ") SQLState(" + SQLstate + ")");
    }
    
    public SQLWarning(String reason) {
        super(reason);
        DriverManager.println("SQLWarning: reason(" + reason + ")");
    }
    
    public SQLWarning() {
        
        DriverManager.println("SQLWarning: ");
    }
    
    public SQLWarning getNextWarning() {
        try {
            return ((SQLWarning)(SQLWarning)getNextException());
        } catch (ClassCastException ex) {
            throw new Error("SQLWarning chain holds value that is not a SQLWarning");
        }
    }
    
    public void setNextWarning(SQLWarning w) {
        setNextException(w);
    }
}
