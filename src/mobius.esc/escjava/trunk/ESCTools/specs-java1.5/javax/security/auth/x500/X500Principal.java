package javax.security.auth.x500;

import java.io.*;
import java.security.Principal;
import sun.security.x509.X500Name;
import sun.security.util.*;

public final class X500Principal implements Principal, java.io.Serializable {
    private static final long serialVersionUID = -500463348111345721L;
    public static final String RFC1779 = "RFC1779";
    public static final String RFC2253 = "RFC2253";
    public static final String CANONICAL = "CANONICAL";
    private transient X500Name thisX500Name;
    
    X500Principal(X500Name x500Name) {
        
        thisX500Name = x500Name;
    }
    
    public X500Principal(String name) {
        
        if (name == null) {
            throw new NullPointerException(sun.security.util.ResourcesMgr.getString("provided null name"));
        }
        try {
            thisX500Name = new X500Name(name);
        } catch (Exception e) {
            IllegalArgumentException iae = new IllegalArgumentException("improperly specified input name: " + name);
            iae.initCause(e);
            throw iae;
        }
    }
    
    public X500Principal(byte[] name) {
        
        try {
            thisX500Name = new X500Name(name);
        } catch (Exception e) {
            IllegalArgumentException iae = new IllegalArgumentException("improperly specified input name");
            iae.initCause(e);
            throw iae;
        }
    }
    
    public X500Principal(InputStream is) {
        
        if (is == null) {
            throw new NullPointerException("provided null input stream");
        }
        try {
            if (is.markSupported()) is.mark(is.available() + 1);
            DerValue der = new DerValue(is);
            thisX500Name = new X500Name(der.data);
        } catch (Exception e) {
            if (is.markSupported()) {
                try {
                    is.reset();
                } catch (IOException ioe) {
                    IllegalArgumentException iae = new IllegalArgumentException("improperly specified input stream " + ("and unable to reset input stream"));
                    iae.initCause(e);
                    throw iae;
                }
            }
            IllegalArgumentException iae = new IllegalArgumentException("improperly specified input stream");
            iae.initCause(e);
            throw iae;
        }
    }
    
    public String getName() {
        return getName(X500Principal.RFC2253);
    }
    
    public String getName(String format) {
        if (format != null) {
            if (format.equalsIgnoreCase(RFC1779)) {
                return thisX500Name.getRFC1779Name();
            } else if (format.equalsIgnoreCase(RFC2253)) {
                return thisX500Name.getRFC2253Name();
            } else if (format.equalsIgnoreCase(CANONICAL)) {
                return thisX500Name.getRFC2253CanonicalName();
            }
        }
        throw new IllegalArgumentException("invalid format specified");
    }
    
    public byte[] getEncoded() {
        try {
            return thisX500Name.getEncoded();
        } catch (IOException e) {
            throw new RuntimeException("unable to get encoding", e);
        }
    }
    
    public String toString() {
        return thisX500Name.toString();
    }
    
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o instanceof X500Principal == false) {
            return false;
        }
        X500Principal other = (X500Principal)(X500Principal)o;
        return this.thisX500Name.equals(other.thisX500Name);
    }
    
    public int hashCode() {
        return thisX500Name.hashCode();
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.writeObject(thisX500Name.getEncodedInternal());
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, java.io.NotActiveException, ClassNotFoundException {
        thisX500Name = new X500Name((byte[])(byte[])s.readObject());
    }
}
