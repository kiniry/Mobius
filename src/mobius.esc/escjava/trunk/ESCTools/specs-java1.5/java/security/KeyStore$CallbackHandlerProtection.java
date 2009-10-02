package java.security;

import java.io.*;
import java.util.*;
import javax.security.auth.callback.*;

public class KeyStore$CallbackHandlerProtection implements KeyStore$ProtectionParameter {
    private final CallbackHandler handler;
    
    public KeyStore$CallbackHandlerProtection(CallbackHandler handler) {
        
        if (handler == null) {
            throw new NullPointerException("handler must not be null");
        }
        this.handler = handler;
    }
    
    public CallbackHandler getCallbackHandler() {
        return handler;
    }
}
