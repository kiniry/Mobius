package com.sun.jmx.mbeanserver;

import java.security.PrivilegedAction;

public class GetPropertyAction implements PrivilegedAction {
    private final String key;
    
    public GetPropertyAction(String key) {
        
        this.key = key;
    }
    
    public Object run() {
        return System.getProperty(key);
    }
}
