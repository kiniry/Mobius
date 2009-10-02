package com.sun.security.auth;

import java.io.*;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.ListIterator;
import java.util.Vector;

class PolicyParser$GrantEntry {
    public String signedBy;
    public String codeBase;
    public LinkedList principals;
    public Vector permissionEntries;
    
    public PolicyParser$GrantEntry() {
        
        permissionEntries = new Vector();
    }
    
    public PolicyParser$GrantEntry(String signedBy, String codeBase) {
        
        this.codeBase = codeBase;
        this.signedBy = signedBy;
        permissionEntries = new Vector();
    }
    
    public void add(PolicyParser$PermissionEntry pe) {
        permissionEntries.addElement(pe);
    }
    
    public boolean remove(PolicyParser$PermissionEntry pe) {
        return permissionEntries.removeElement(pe);
    }
    
    public boolean contains(PolicyParser$PermissionEntry pe) {
        return permissionEntries.contains(pe);
    }
    
    public Enumeration permissionElements() {
        return permissionEntries.elements();
    }
    
    public void write(PrintWriter out) {
        out.print("grant");
        if (signedBy != null) {
            out.print(" signedBy \"");
            out.print(signedBy);
            out.print('\"');
            if (codeBase != null) out.print(", ");
        }
        if (codeBase != null) {
            out.print(" codeBase \"");
            out.print(codeBase);
            out.print('\"');
            if (principals != null && principals.size() > 0) out.print(",\n");
        }
        if (principals != null && principals.size() > 0) {
            ListIterator pli = principals.listIterator();
            while (pli.hasNext()) {
                out.print("\tPrincipal ");
                PolicyParser$PrincipalEntry pe = (PolicyParser$PrincipalEntry)(PolicyParser$PrincipalEntry)pli.next();
                out.print((String)pe.principalClass + " \"" + pe.principalName + "\"");
                if (pli.hasNext()) out.print(",\n");
            }
        }
        out.println(" {");
        Enumeration enum_ = permissionEntries.elements();
        while (enum_.hasMoreElements()) {
            PolicyParser$PermissionEntry pe = (PolicyParser$PermissionEntry)(PolicyParser$PermissionEntry)enum_.nextElement();
            out.write("  ");
            pe.write(out);
        }
        out.println("};");
    }
}
