package com.sun.security.auth;

public interface PrincipalComparator {
    
    boolean implies(javax.security.auth.Subject subject);
}
