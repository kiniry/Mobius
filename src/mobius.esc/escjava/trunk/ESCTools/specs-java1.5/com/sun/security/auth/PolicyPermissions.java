package com.sun.security.auth;

import java.io.*;
import java.lang.reflect.*;
import java.util.*;
import java.security.CodeSource;
import java.security.Permission;
import java.security.Permissions;
import java.security.PermissionCollection;

class PolicyPermissions extends PermissionCollection {
    private static final long serialVersionUID = -1954188373270545523L;
    private CodeSource codesource;
    private Permissions perms;
    private PolicyFile policy;
    private boolean notInit;
    private Vector additionalPerms;
    
    PolicyPermissions(PolicyFile policy, CodeSource codesource) {
        
        this.codesource = codesource;
        this.policy = policy;
        this.perms = null;
        this.notInit = true;
        this.additionalPerms = null;
    }
    
    public void add(Permission permission) {
        if (isReadOnly()) throw new SecurityException(PolicyFile.rb.getString("attempt to add a Permission to a readonly PermissionCollection"));
        if (perms == null) {
            if (additionalPerms == null) additionalPerms = new Vector();
            additionalPerms.add(permission);
        } else {
            perms.add(permission);
        }
    }
    
    private synchronized void init() {
        if (notInit) {
            if (perms == null) perms = new Permissions();
            if (additionalPerms != null) {
                Enumeration e = additionalPerms.elements();
                while (e.hasMoreElements()) {
                    perms.add((Permission)(Permission)e.nextElement());
                }
                additionalPerms = null;
            }
            policy.getPermissions(perms, codesource);
            notInit = false;
        }
    }
    
    public boolean implies(Permission permission) {
        if (notInit) init();
        return perms.implies(permission);
    }
    
    public Enumeration elements() {
        if (notInit) init();
        return perms.elements();
    }
    
    public String toString() {
        if (notInit) init();
        return perms.toString();
    }
}
