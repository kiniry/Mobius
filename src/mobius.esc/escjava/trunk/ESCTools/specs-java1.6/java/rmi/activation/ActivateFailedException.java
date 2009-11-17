package java.rmi.activation;

public class ActivateFailedException extends java.rmi.RemoteException {
    private static final long serialVersionUID = 4863550261346652506L;
    
    public ActivateFailedException(String s) {
        super(s);
    }
    
    public ActivateFailedException(String s, Exception ex) {
        super(s, ex);
    }
}
