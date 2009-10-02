package java.nio.charset;

public class CoderMalfunctionError extends Error {
    
    public CoderMalfunctionError(Exception cause) {
        super(cause);
    }
}
