package java.sql;

public class BatchUpdateException extends SQLException {
    
    public BatchUpdateException(String reason, String SQLState, int vendorCode, int[] updateCounts) {
        super(reason, SQLState, vendorCode);
        this.updateCounts = updateCounts;
    }
    
    public BatchUpdateException(String reason, String SQLState, int[] updateCounts) {
        super(reason, SQLState);
        this.updateCounts = updateCounts;
    }
    
    public BatchUpdateException(String reason, int[] updateCounts) {
        super(reason);
        this.updateCounts = updateCounts;
    }
    
    public BatchUpdateException(int[] updateCounts) {
        
        this.updateCounts = updateCounts;
    }
    
    public BatchUpdateException() {
        
        this.updateCounts = null;
    }
    
    public int[] getUpdateCounts() {
        return updateCounts;
    }
    private int[] updateCounts;
}
