package javax.security.auth;

import java.util.*;
import java.io.*;
import java.lang.reflect.*;
import java.security.AccessController;
import java.security.AccessControlContext;
import java.security.Principal;
import java.security.ProtectionDomain;
import sun.security.util.ResourcesMgr;
import sun.security.util.SecurityConstants;

public final class Subject implements java.io.Serializable {
    private static final long serialVersionUID = -8308522755600156056L;
    Set principals;
    transient Set pubCredentials;
    transient Set privCredentials;
    private volatile boolean readOnly = false;
    private static final int PRINCIPAL_SET = 1;
    private static final int PUB_CREDENTIAL_SET = 2;
    private static final int PRIV_CREDENTIAL_SET = 3;
    
    public Subject() {
        
        this.principals = Collections.synchronizedSet(new Subject$SecureSet(this, PRINCIPAL_SET));
        this.pubCredentials = Collections.synchronizedSet(new Subject$SecureSet(this, PUB_CREDENTIAL_SET));
        this.privCredentials = Collections.synchronizedSet(new Subject$SecureSet(this, PRIV_CREDENTIAL_SET));
    }
    
    public Subject(boolean readOnly, Set principals, Set pubCredentials, Set privCredentials) {
        
        if (principals == null || pubCredentials == null || privCredentials == null) throw new NullPointerException(ResourcesMgr.getString("invalid null input(s)"));
        this.principals = Collections.synchronizedSet(new Subject$SecureSet(this, PRINCIPAL_SET, principals));
        this.pubCredentials = Collections.synchronizedSet(new Subject$SecureSet(this, PUB_CREDENTIAL_SET, pubCredentials));
        this.privCredentials = Collections.synchronizedSet(new Subject$SecureSet(this, PRIV_CREDENTIAL_SET, privCredentials));
        this.readOnly = readOnly;
    }
    
    public void setReadOnly() {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(new AuthPermission("setReadOnly"));
        }
        this.readOnly = true;
    }
    
    public boolean isReadOnly() {
        return this.readOnly;
    }
    
    public static Subject getSubject(final AccessControlContext acc) {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(new AuthPermission("getSubject"));
        }
        if (acc == null) {
            throw new NullPointerException(ResourcesMgr.getString("invalid null AccessControlContext provided"));
        }
        return (Subject)(Subject)AccessController.doPrivileged(new Subject$1(acc));
    }
    
    public static Object doAs(final Subject subject, final java.security.PrivilegedAction action) {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.DO_AS_PERMISSION);
        }
        if (action == null) throw new NullPointerException(ResourcesMgr.getString("invalid null action provided"));
        final AccessControlContext currentAcc = AccessController.getContext();
        return java.security.AccessController.doPrivileged(action, createContext(subject, currentAcc));
    }
    
    public static Object doAs(final Subject subject, final java.security.PrivilegedExceptionAction action) throws java.security.PrivilegedActionException {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.DO_AS_PERMISSION);
        }
        if (action == null) throw new NullPointerException(ResourcesMgr.getString("invalid null action provided"));
        final AccessControlContext currentAcc = AccessController.getContext();
        return java.security.AccessController.doPrivileged(action, createContext(subject, currentAcc));
    }
    
    public static Object doAsPrivileged(final Subject subject, final java.security.PrivilegedAction action, final java.security.AccessControlContext acc) {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.DO_AS_PRIVILEGED_PERMISSION);
        }
        if (action == null) throw new NullPointerException(ResourcesMgr.getString("invalid null action provided"));
        final AccessControlContext callerAcc = (acc == null ? new AccessControlContext(new ProtectionDomain[0]) : acc);
        return java.security.AccessController.doPrivileged(action, createContext(subject, callerAcc));
    }
    
    public static Object doAsPrivileged(final Subject subject, final java.security.PrivilegedExceptionAction action, final java.security.AccessControlContext acc) throws java.security.PrivilegedActionException {
        java.lang.SecurityManager sm = System.getSecurityManager();
        if (sm != null) {
            sm.checkPermission(SecurityConstants.DO_AS_PRIVILEGED_PERMISSION);
        }
        if (action == null) throw new NullPointerException(ResourcesMgr.getString("invalid null action provided"));
        final AccessControlContext callerAcc = (acc == null ? new AccessControlContext(new ProtectionDomain[0]) : acc);
        return java.security.AccessController.doPrivileged(action, createContext(subject, callerAcc));
    }
    
    private static AccessControlContext createContext(final Subject subject, final AccessControlContext acc) {
        return (AccessControlContext)(AccessControlContext)java.security.AccessController.doPrivileged(new Subject$2(subject, acc));
    }
    
    public Set getPrincipals() {
        return principals;
    }
    
    public Set getPrincipals(Class c) {
        if (c == null) throw new NullPointerException(ResourcesMgr.getString("invalid null Class provided"));
        return new Subject$ClassSet(this, PRINCIPAL_SET, c);
    }
    
    public Set getPublicCredentials() {
        return pubCredentials;
    }
    
    public Set getPrivateCredentials() {
        return privCredentials;
    }
    
    public Set getPublicCredentials(Class c) {
        if (c == null) throw new NullPointerException(ResourcesMgr.getString("invalid null Class provided"));
        return new Subject$ClassSet(this, PUB_CREDENTIAL_SET, c);
    }
    
    public Set getPrivateCredentials(Class c) {
        if (c == null) throw new NullPointerException(ResourcesMgr.getString("invalid null Class provided"));
        return new Subject$ClassSet(this, PRIV_CREDENTIAL_SET, c);
    }
    
    public boolean equals(Object o) {
        if (o == null) return false;
        if (this == o) return true;
        if (o instanceof Subject) {
            final Subject that = (Subject)(Subject)o;
            Set thatPrincipals;
            synchronized (that.principals) {
                thatPrincipals = new HashSet(that.principals);
            }
            if (!principals.equals(thatPrincipals)) {
                return false;
            }
            Set thatPubCredentials;
            synchronized (that.pubCredentials) {
                thatPubCredentials = new HashSet(that.pubCredentials);
            }
            if (!pubCredentials.equals(thatPubCredentials)) {
                return false;
            }
            Set thatPrivCredentials;
            synchronized (that.privCredentials) {
                thatPrivCredentials = new HashSet(that.privCredentials);
            }
            if (!privCredentials.equals(thatPrivCredentials)) {
                return false;
            }
            return true;
        }
        return false;
    }
    
    public String toString() {
        return toString(true);
    }
    
    String toString(boolean includePrivateCredentials) {
        String s = new String(ResourcesMgr.getString("Subject:\n"));
        String suffix = new String();
        synchronized (principals) {
            Iterator pI = principals.iterator();
            while (pI.hasNext()) {
                Principal p = (Principal)(Principal)pI.next();
                suffix = suffix + ResourcesMgr.getString("\tPrincipal: ") + p.toString() + ResourcesMgr.getString("\n");
            }
        }
        synchronized (pubCredentials) {
            Iterator pI = pubCredentials.iterator();
            while (pI.hasNext()) {
                Object o = pI.next();
                suffix = suffix + ResourcesMgr.getString("\tPublic Credential: ") + o.toString() + ResourcesMgr.getString("\n");
            }
        }
        if (includePrivateCredentials) {
            synchronized (privCredentials) {
                Iterator pI = privCredentials.iterator();
                while (pI.hasNext()) {
                    try {
                        Object o = pI.next();
                        suffix += ResourcesMgr.getString("\tPrivate Credential: ") + o.toString() + ResourcesMgr.getString("\n");
                    } catch (SecurityException se) {
                        suffix += ResourcesMgr.getString("\tPrivate Credential inaccessible\n");
                        break;
                    }
                }
            }
        }
        return s + suffix;
    }
    
    public int hashCode() {
        int hashCode = 0;
        synchronized (principals) {
            Iterator pIterator = principals.iterator();
            while (pIterator.hasNext()) {
                Principal p = (Principal)(Principal)pIterator.next();
                hashCode ^= p.hashCode();
            }
        }
        synchronized (pubCredentials) {
            Iterator pubCIterator = pubCredentials.iterator();
            while (pubCIterator.hasNext()) {
                hashCode ^= getCredHashCode(pubCIterator.next());
            }
        }
        return hashCode;
    }
    
    private int getCredHashCode(Object o) {
        try {
            return o.hashCode();
        } catch (IllegalStateException ise) {
            return o.getClass().toString().hashCode();
        }
    }
    
    private void writeObject(java.io.ObjectOutputStream oos) throws java.io.IOException {
        synchronized (principals) {
            oos.defaultWriteObject();
        }
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        this.pubCredentials = Collections.synchronizedSet(new Subject$SecureSet(this, PUB_CREDENTIAL_SET));
        this.privCredentials = Collections.synchronizedSet(new Subject$SecureSet(this, PRIV_CREDENTIAL_SET));
    }
    {
    }
    {
    }
}
