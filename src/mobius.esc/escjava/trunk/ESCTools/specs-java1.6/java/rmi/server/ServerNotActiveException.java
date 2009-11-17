package java.rmi.server;

public class ServerNotActiveException extends java.lang.Exception {
    private static final long serialVersionUID = 4687940720827538231L;
    
    public ServerNotActiveException() {
        
    }
    
    public ServerNotActiveException(String s) {
        super(s);
    }
}
