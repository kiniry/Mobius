package java.rmi.server;

public class SocketSecurityException extends ExportException {
    private static final long serialVersionUID = -7622072999407781979L;
    
    public SocketSecurityException(String s) {
        super(s);
    }
    
    public SocketSecurityException(String s, Exception ex) {
        super(s, ex);
    }
}
