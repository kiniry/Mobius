package javax.security.auth.callback;

public interface CallbackHandler {
    
    void handle(Callback[] callbacks) throws java.io.IOException, UnsupportedCallbackException;
}
