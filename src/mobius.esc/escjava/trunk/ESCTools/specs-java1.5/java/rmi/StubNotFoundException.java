package java.rmi;

public class StubNotFoundException extends RemoteException {
    private static final long serialVersionUID = -7088199405468872373L;
    
    public StubNotFoundException(String s) {
        super(s);
    }
    
    public StubNotFoundException(String s, Exception ex) {
        super(s, ex);
    }
}
