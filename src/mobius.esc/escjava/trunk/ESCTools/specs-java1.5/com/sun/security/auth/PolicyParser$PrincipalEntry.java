package com.sun.security.auth;

import java.io.*;

class PolicyParser$PrincipalEntry {
    static final String WILDCARD_CLASS = "WILDCARD_PRINCIPAL_CLASS";
    static final String WILDCARD_NAME = "WILDCARD_PRINCIPAL_NAME";
    String principalClass;
    String principalName;
    
    public PolicyParser$PrincipalEntry(String principalClass, String principalName) {
        
        if (principalClass == null || principalName == null) throw new NullPointerException("null principalClass or principalName");
        this.principalClass = principalClass;
        this.principalName = principalName;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof PolicyParser$PrincipalEntry)) return false;
        PolicyParser$PrincipalEntry that = (PolicyParser$PrincipalEntry)(PolicyParser$PrincipalEntry)obj;
        if (this.principalClass.equals(that.principalClass) && this.principalName.equals(that.principalName)) {
            return true;
        }
        return false;
    }
    
    public int hashCode() {
        return principalClass.hashCode();
    }
}
