package java.security;

import javax.security.auth.Subject;
import javax.security.auth.login.LoginException;
import javax.security.auth.callback.CallbackHandler;

public abstract class AuthProvider extends Provider {
    
    protected AuthProvider(String name, double version, String info) {
        super(name, version, info);
    }
    
    public abstract void login(Subject subject, CallbackHandler handler) throws LoginException;
    
    public abstract void logout() throws LoginException;
    
    public abstract void setCallbackHandler(CallbackHandler handler);
}
