package java.rmi;

public class UnknownHostException extends RemoteException {
    private static final long serialVersionUID = -8152710247442114228L;
    
    public UnknownHostException(String s) {
        super(s);
    }
    
    public UnknownHostException(String s, Exception ex) {
        super(s, ex);
    }
}
