package com.sun.security.auth;

import java.util.*;

class SubjectCodeSource$1 implements java.security.PrivilegedAction {
    
    SubjectCodeSource$1() {
        
    }
    
    public Object run() {
        return (java.util.ResourceBundle.getBundle("sun.security.util.AuthResources"));
    }
}
