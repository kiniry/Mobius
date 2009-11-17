package java.net;

public class SocketTimeoutException extends java.io.InterruptedIOException {
    
    public SocketTimeoutException(String msg) {
        super(msg);
    }
    
    public SocketTimeoutException() {
        
    }
}
