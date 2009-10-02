package java.rmi;

public class ConnectIOException extends RemoteException {
    private static final long serialVersionUID = -8087809532704668744L;
    
    public ConnectIOException(String s) {
        super(s);
    }
    
    public ConnectIOException(String s, Exception ex) {
        super(s, ex);
    }
}
