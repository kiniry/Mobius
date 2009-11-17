package java.rmi;


public class RMISecurityException extends java.lang.SecurityException {
    private static final long serialVersionUID = -8433406075740433514L;
    
    
    public RMISecurityException(String name) {
        super(name);
    }
    
    
    public RMISecurityException(String name, String arg) {
        this(name);
    }
}
