package java.io;

public class InterruptedIOException extends IOException {
    
    public InterruptedIOException() {
        
    }
    
    public InterruptedIOException(String s) {
        super(s);
    }
    public int bytesTransferred = 0;
}
