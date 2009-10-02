package java.rmi;

public class AccessException extends java.rmi.RemoteException {
    private static final long serialVersionUID = 6314925228044966088L;
    
    public AccessException(String s) {
        super(s);
    }
    
    public AccessException(String s, Exception ex) {
        super(s, ex);
    }
}
