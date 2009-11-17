package java.security;

import java.io.IOException;
import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Hashtable;
import java.lang.reflect.*;
import java.security.cert.*;

public final class UnresolvedPermission extends Permission implements java.io.Serializable {
    private static final long serialVersionUID = -4821973115467008846L;
    private static final sun.security.util.Debug debug = sun.security.util.Debug.getInstance("policy,access", "UnresolvedPermission");
    private String type;
    private String name;
    private String actions;
    private transient java.security.cert.Certificate[] certs;
    
    public UnresolvedPermission(String type, String name, String actions, java.security.cert.Certificate[] certs) {
        super(type);
        if (type == null) throw new NullPointerException("type can\'t be null");
        this.type = type;
        this.name = name;
        this.actions = actions;
        if (certs != null) {
            for (int i = 0; i < certs.length; i++) {
                if (!(certs[i] instanceof X509Certificate)) {
                    this.certs = (java.security.cert.Certificate[])(java.security.cert.Certificate[])certs.clone();
                    break;
                }
            }
            if (this.certs == null) {
                int i = 0;
                int count = 0;
                while (i < certs.length) {
                    count++;
                    while (((i + 1) < certs.length) && ((X509Certificate)(X509Certificate)certs[i]).getIssuerDN().equals(((X509Certificate)(X509Certificate)certs[i + 1]).getSubjectDN())) {
                        i++;
                    }
                    i++;
                }
                if (count == certs.length) {
                    this.certs = (java.security.cert.Certificate[])(java.security.cert.Certificate[])certs.clone();
                }
                if (this.certs == null) {
                    ArrayList signerCerts = new ArrayList();
                    i = 0;
                    while (i < certs.length) {
                        signerCerts.add(certs[i]);
                        while (((i + 1) < certs.length) && ((X509Certificate)(X509Certificate)certs[i]).getIssuerDN().equals(((X509Certificate)(X509Certificate)certs[i + 1]).getSubjectDN())) {
                            i++;
                        }
                        i++;
                    }
                    this.certs = new java.security.cert.Certificate[signerCerts.size()];
                    signerCerts.toArray(this.certs);
                }
            }
        }
    }
    private static final Class[] PARAMS0 = {};
    private static final Class[] PARAMS1 = {String.class};
    private static final Class[] PARAMS2 = {String.class, String.class};
    
    Permission resolve(Permission p, java.security.cert.Certificate[] certs) {
        if (this.certs != null) {
            if (certs == null) {
                return null;
            }
            boolean match;
            for (int i = 0; i < this.certs.length; i++) {
                match = false;
                for (int j = 0; j < certs.length; j++) {
                    if (this.certs[i].equals(certs[j])) {
                        match = true;
                        break;
                    }
                }
                if (!match) return null;
            }
        }
        try {
            Class pc = p.getClass();
            if (name == null && actions == null) {
                try {
                    Constructor c = pc.getConstructor(PARAMS0);
                    return (Permission)(Permission)c.newInstance(new Object[]{});
                } catch (NoSuchMethodException ne) {
                    try {
                        Constructor c = pc.getConstructor(PARAMS1);
                        return (Permission)(Permission)c.newInstance(new Object[]{name});
                    } catch (NoSuchMethodException ne1) {
                        Constructor c = pc.getConstructor(PARAMS2);
                        return (Permission)(Permission)c.newInstance(new Object[]{name, actions});
                    }
                }
            } else {
                if (name != null && actions == null) {
                    try {
                        Constructor c = pc.getConstructor(PARAMS1);
                        return (Permission)(Permission)c.newInstance(new Object[]{name});
                    } catch (NoSuchMethodException ne) {
                        Constructor c = pc.getConstructor(PARAMS2);
                        return (Permission)(Permission)c.newInstance(new Object[]{name, actions});
                    }
                } else {
                    Constructor c = pc.getConstructor(PARAMS2);
                    return (Permission)(Permission)c.newInstance(new Object[]{name, actions});
                }
            }
        } catch (NoSuchMethodException nsme) {
            if (debug != null) {
                debug.println("NoSuchMethodException:\n  could not find " + "proper constructor for " + type);
                nsme.printStackTrace();
            }
            return null;
        } catch (Exception e) {
            if (debug != null) {
                debug.println("unable to instantiate " + name);
                e.printStackTrace();
            }
            return null;
        }
    }
    
    public boolean implies(Permission p) {
        return false;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof UnresolvedPermission)) return false;
        UnresolvedPermission that = (UnresolvedPermission)(UnresolvedPermission)obj;
        if (!this.type.equals(that.type)) {
            return false;
        }
        if (this.name == null) {
            if (that.name != null) {
                return false;
            }
        } else if (!this.name.equals(that.name)) {
            return false;
        }
        if (this.actions == null) {
            if (that.actions != null) {
                return false;
            }
        } else {
            if (!this.actions.equals(that.actions)) {
                return false;
            }
        }
        if ((this.certs == null && that.certs != null) || (this.certs != null && that.certs == null) || (this.certs != null && that.certs != null && this.certs.length != that.certs.length)) {
            return false;
        }
        int i;
        int j;
        boolean match;
        for (i = 0; this.certs != null && i < this.certs.length; i++) {
            match = false;
            for (j = 0; j < that.certs.length; j++) {
                if (this.certs[i].equals(that.certs[j])) {
                    match = true;
                    break;
                }
            }
            if (!match) return false;
        }
        for (i = 0; that.certs != null && i < that.certs.length; i++) {
            match = false;
            for (j = 0; j < this.certs.length; j++) {
                if (that.certs[i].equals(this.certs[j])) {
                    match = true;
                    break;
                }
            }
            if (!match) return false;
        }
        return true;
    }
    
    public int hashCode() {
        int hash = type.hashCode();
        if (name != null) hash ^= name.hashCode();
        if (actions != null) hash ^= actions.hashCode();
        return hash;
    }
    
    public String getActions() {
        return "";
    }
    
    public String getUnresolvedType() {
        return type;
    }
    
    public String getUnresolvedName() {
        return name;
    }
    
    public String getUnresolvedActions() {
        return actions;
    }
    
    public java.security.cert.Certificate[] getUnresolvedCerts() {
        return (certs == null) ? null : (java.security.cert.Certificate[])(java.security.cert.Certificate[])certs.clone();
    }
    
    public String toString() {
        return "(unresolved " + type + " " + name + " " + actions + ")";
    }
    
    public PermissionCollection newPermissionCollection() {
        return new UnresolvedPermissionCollection();
    }
    
    private synchronized void writeObject(java.io.ObjectOutputStream oos) throws IOException {
        oos.defaultWriteObject();
        if (certs == null || certs.length == 0) {
            oos.writeInt(0);
        } else {
            oos.writeInt(certs.length);
            for (int i = 0; i < certs.length; i++) {
                java.security.cert.Certificate cert = certs[i];
                try {
                    oos.writeUTF(cert.getType());
                    byte[] encoded = cert.getEncoded();
                    oos.writeInt(encoded.length);
                    oos.write(encoded);
                } catch (CertificateEncodingException cee) {
                    throw new IOException(cee.getMessage());
                }
            }
        }
    }
    
    private synchronized void readObject(java.io.ObjectInputStream ois) throws IOException, ClassNotFoundException {
        CertificateFactory cf;
        Hashtable cfs = null;
        ois.defaultReadObject();
        if (type == null) throw new NullPointerException("type can\'t be null");
        int size = ois.readInt();
        if (size > 0) {
            cfs = new Hashtable(3);
            this.certs = new java.security.cert.Certificate[size];
        }
        for (int i = 0; i < size; i++) {
            String certType = ois.readUTF();
            if (cfs.containsKey(certType)) {
                cf = (CertificateFactory)(CertificateFactory)cfs.get(certType);
            } else {
                try {
                    cf = CertificateFactory.getInstance(certType);
                } catch (CertificateException ce) {
                    throw new ClassNotFoundException("Certificate factory for " + certType + " not found");
                }
                cfs.put(certType, cf);
            }
            byte[] encoded = null;
            try {
                encoded = new byte[ois.readInt()];
            } catch (OutOfMemoryError oome) {
                throw new IOException("Certificate too big");
            }
            ois.readFully(encoded);
            ByteArrayInputStream bais = new ByteArrayInputStream(encoded);
            try {
                this.certs[i] = cf.generateCertificate(bais);
            } catch (CertificateException ce) {
                throw new IOException(ce.getMessage());
            }
            bais.close();
        }
    }
}
