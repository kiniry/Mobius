package com.sun.security.auth;

import java.io.*;
import java.lang.reflect.*;
import java.util.*;
import java.security.CodeSource;
import java.security.Permission;

class PolicyFile$PolicyEntry {
    CodeSource codesource;
    Vector permissions;
    
    PolicyFile$PolicyEntry(CodeSource cs) {
        
        this.codesource = cs;
        this.permissions = new Vector();
    }
    
    void add(Permission p) {
        permissions.addElement(p);
    }
    
    CodeSource getCodeSource() {
        return this.codesource;
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append(PolicyFile.rb.getString("("));
        sb.append(getCodeSource());
        sb.append("\n");
        for (int j = 0; j < permissions.size(); j++) {
            Permission p = (Permission)(Permission)permissions.elementAt(j);
            sb.append(PolicyFile.rb.getString(" "));
            sb.append(PolicyFile.rb.getString(" "));
            sb.append(p);
            sb.append(PolicyFile.rb.getString("\n"));
        }
        sb.append(PolicyFile.rb.getString(")"));
        sb.append(PolicyFile.rb.getString("\n"));
        return sb.toString();
    }
}
