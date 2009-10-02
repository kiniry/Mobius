package com.sun.security.auth;

import java.io.*;

class PolicyParser$PermissionEntry {
    public String permission;
    public String name;
    public String action;
    public String signedBy;
    
    public PolicyParser$PermissionEntry() {
        
    }
    
    public PolicyParser$PermissionEntry(String permission, String name, String action) {
        
        this.permission = permission;
        this.name = name;
        this.action = action;
    }
    
    public int hashCode() {
        int retval = permission.hashCode();
        if (name != null) retval ^= name.hashCode();
        if (action != null) retval ^= action.hashCode();
        return retval;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof PolicyParser$PermissionEntry)) return false;
        PolicyParser$PermissionEntry that = (PolicyParser$PermissionEntry)(PolicyParser$PermissionEntry)obj;
        if (this.permission == null) {
            if (that.permission != null) return false;
        } else {
            if (!this.permission.equals(that.permission)) return false;
        }
        if (this.name == null) {
            if (that.name != null) return false;
        } else {
            if (!this.name.equals(that.name)) return false;
        }
        if (this.action == null) {
            if (that.action != null) return false;
        } else {
            if (!this.action.equals(that.action)) return false;
        }
        if (this.signedBy == null) {
            if (that.signedBy != null) return false;
        } else {
            if (!this.signedBy.equals(that.signedBy)) return false;
        }
        return true;
    }
    
    public void write(PrintWriter out) {
        out.print("permission ");
        out.print(permission);
        if (name != null) {
            out.print(" \"");
            if (name.indexOf("\"") != -1) {
                int numQuotes = 0;
                char[] chars = name.toCharArray();
                for (int i = 0; i < chars.length; i++) {
                    if (chars[i] == '\"') numQuotes++;
                }
                char[] newChars = new char[chars.length + numQuotes];
                for (int i = 0, j = 0; i < chars.length; i++) {
                    if (chars[i] != '\"') {
                        newChars[j++] = chars[i];
                    } else {
                        newChars[j++] = '\\';
                        newChars[j++] = chars[i];
                    }
                }
                name = new String(newChars);
            }
            out.print(name);
            out.print('\"');
        }
        if (action != null) {
            out.print(", \"");
            out.print(action);
            out.print('\"');
        }
        if (signedBy != null) {
            out.print(", signedBy \"");
            out.print(signedBy);
            out.print('\"');
        }
        out.println(";");
    }
}
