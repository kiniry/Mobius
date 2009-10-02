package java.lang;

public class AssertionError extends Error {
    
    public AssertionError() {
        
    }
    
    private AssertionError(String detailMessage) {
        super(detailMessage);
    }
    
    public AssertionError(Object detailMessage) {
        this("" + detailMessage);
        if (detailMessage instanceof Throwable) initCause((Throwable)(Throwable)detailMessage);
    }
    
    public AssertionError(boolean detailMessage) {
        this("" + detailMessage);
    }
    
    public AssertionError(char detailMessage) {
        this("" + detailMessage);
    }
    
    public AssertionError(int detailMessage) {
        this("" + detailMessage);
    }
    
    public AssertionError(long detailMessage) {
        this("" + detailMessage);
    }
    
    public AssertionError(float detailMessage) {
        this("" + detailMessage);
    }
    
    public AssertionError(double detailMessage) {
        this("" + detailMessage);
    }
}
