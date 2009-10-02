package javax.security.auth.login;

public class LoginException extends java.security.GeneralSecurityException {
    private static final long serialVersionUID = -4679091624035232488L;
    
    public LoginException() {
        
    }
    
    public LoginException(String msg) {
        super(msg);
    }
}
