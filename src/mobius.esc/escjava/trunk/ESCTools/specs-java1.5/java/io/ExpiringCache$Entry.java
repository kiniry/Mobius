package java.io;

class ExpiringCache$Entry {
    private long timestamp;
    private String val;
    
    ExpiringCache$Entry(long timestamp, String val) {
        
        this.timestamp = timestamp;
        this.val = val;
    }
    
    long timestamp() {
        return timestamp;
    }
    
    void setTimestamp(long timestamp) {
        this.timestamp = timestamp;
    }
    
    String val() {
        return val;
    }
    
    void setVal(String val) {
        this.val = val;
    }
}
