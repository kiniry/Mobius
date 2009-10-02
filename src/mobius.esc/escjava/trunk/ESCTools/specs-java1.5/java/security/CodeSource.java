package java.security;

import java.net.URL;
import java.net.SocketPermission;
import java.util.ArrayList;
import java.util.List;
import java.util.Hashtable;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.security.cert.*;

public class CodeSource implements java.io.Serializable {
    private static final long serialVersionUID = 4977541819976013951L;
    private URL location;
    private transient CodeSigner[] signers = null;
    private transient java.security.cert.Certificate[] certs = null;
    private transient SocketPermission sp;
    private transient CertificateFactory factory = null;
    
    public CodeSource(URL url, java.security.cert.Certificate[] certs) {
        
        this.location = url;
        if (certs != null) {
            this.certs = (java.security.cert.Certificate[])(java.security.cert.Certificate[])certs.clone();
        }
    }
    
    public CodeSource(URL url, CodeSigner[] signers) {
        
        this.location = url;
        if (signers != null) {
            this.signers = (CodeSigner[])(CodeSigner[])signers.clone();
        }
    }
    
    public int hashCode() {
        if (location != null) return location.hashCode(); else return 0;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof CodeSource)) return false;
        CodeSource cs = (CodeSource)(CodeSource)obj;
        if (location == null) {
            if (cs.location != null) return false;
        } else {
            if (!location.equals(cs.location)) return false;
        }
        return matchCerts(cs, true);
    }
    
    public final URL getLocation() {
        return this.location;
    }
    
    public final java.security.cert.Certificate[] getCertificates() {
        if (certs != null) {
            return (java.security.cert.Certificate[])(java.security.cert.Certificate[])certs.clone();
        } else if (signers != null) {
            ArrayList certChains = new ArrayList();
            for (int i = 0; i < signers.length; i++) {
                certChains.addAll(signers[i].getSignerCertPath().getCertificates());
            }
            certs = (java.security.cert.Certificate[])(java.security.cert.Certificate[])certChains.toArray(new java.security.cert.Certificate[certChains.size()]);
            return (java.security.cert.Certificate[])(java.security.cert.Certificate[])certs.clone();
        } else {
            return null;
        }
    }
    
    public final CodeSigner[] getCodeSigners() {
        if (signers != null) {
            return (CodeSigner[])(CodeSigner[])signers.clone();
        } else if (certs != null) {
            signers = convertCertArrayToSignerArray(certs);
            return (CodeSigner[])(CodeSigner[])signers.clone();
        } else {
            return null;
        }
    }
    
    public boolean implies(CodeSource codesource) {
        if (codesource == null) return false;
        return matchCerts(codesource, false) && matchLocation(codesource);
    }
    
    private boolean matchCerts(CodeSource that, boolean strict) {
        if (certs == null && signers == null) return true;
        if (that.certs == null && that.signers == null) return false;
        boolean match;
        if (signers != null && that.signers != null) {
            if (strict && signers.length != that.signers.length) {
                return false;
            }
            for (int i = 0; i < signers.length; i++) {
                match = false;
                for (int j = 0; j < that.signers.length; j++) {
                    if (signers[i].equals(that.signers[j])) {
                        match = true;
                        break;
                    }
                }
                if (!match) return false;
            }
            return true;
        } else {
            if (strict && certs.length != that.certs.length) {
                return false;
            }
            for (int i = 0; i < certs.length; i++) {
                match = false;
                for (int j = 0; j < that.certs.length; j++) {
                    if (certs[i].equals(that.certs[j])) {
                        match = true;
                        break;
                    }
                }
                if (!match) return false;
            }
            return true;
        }
    }
    
    private boolean matchLocation(CodeSource that) {
        if (location == null) {
            return true;
        }
        if ((that == null) || (that.location == null)) return false;
        if (location.equals(that.location)) return true;
        if (!location.getProtocol().equals(that.location.getProtocol())) return false;
        String thisHost = location.getHost();
        String thatHost = that.location.getHost();
        if (thisHost != null) {
            if (("".equals(thisHost) || "localhost".equals(thisHost)) && ("".equals(thatHost) || "localhost".equals(thatHost))) {
            } else if (!thisHost.equals(thatHost)) {
                if (thatHost == null) {
                    return false;
                }
                if (this.sp == null) {
                    this.sp = new SocketPermission(thisHost, "resolve");
                }
                if (that.sp == null) {
                    that.sp = new SocketPermission(thatHost, "resolve");
                }
                if (!this.sp.implies(that.sp)) {
                    return false;
                }
            }
        }
        if (location.getPort() != -1) {
            if (location.getPort() != that.location.getPort()) return false;
        }
        if (location.getFile().endsWith("/-")) {
            String thisPath = location.getFile().substring(0, location.getFile().length() - 1);
            if (!that.location.getFile().startsWith(thisPath)) return false;
        } else if (location.getFile().endsWith("/*")) {
            int last = that.location.getFile().lastIndexOf('/');
            if (last == -1) return false;
            String thisPath = location.getFile().substring(0, location.getFile().length() - 1);
            String thatPath = that.location.getFile().substring(0, last + 1);
            if (!thatPath.equals(thisPath)) return false;
        } else {
            if ((!that.location.getFile().equals(location.getFile())) && (!that.location.getFile().equals(location.getFile() + "/"))) {
                return false;
            }
        }
        if (location.getRef() == null) return true; else return location.getRef().equals(that.location.getRef());
    }
    
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("(");
        sb.append(this.location);
        if (this.certs != null && this.certs.length > 0) {
            for (int i = 0; i < this.certs.length; i++) {
                sb.append(" " + this.certs[i]);
            }
        } else if (this.signers != null && this.signers.length > 0) {
            for (int i = 0; i < this.signers.length; i++) {
                sb.append(" " + this.signers[i]);
            }
        } else {
            sb.append(" <no signer certificates>");
        }
        sb.append(")");
        return sb.toString();
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
        if (signers != null && signers.length > 0) {
            oos.writeObject(signers);
        }
    }
    
    private synchronized void readObject(java.io.ObjectInputStream ois) throws IOException, ClassNotFoundException {
        CertificateFactory cf;
        Hashtable cfs = null;
        ois.defaultReadObject();
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
        try {
            this.signers = (CodeSigner[])(CodeSigner[])ois.readObject();
        } catch (IOException ioe) {
        }
    }
    
    private CodeSigner[] convertCertArrayToSignerArray(java.security.cert.Certificate[] certs) {
        if (certs == null) {
            return null;
        }
        try {
            if (factory == null) {
                factory = CertificateFactory.getInstance("X.509");
            }
            int i = 0;
            List signers = new ArrayList();
            while (i < certs.length) {
                List certChain = new ArrayList();
                certChain.add(certs[i++]);
                int j = i;
                while (j < certs.length && certs[j] instanceof X509Certificate && ((X509Certificate)(X509Certificate)certs[j]).getBasicConstraints() != -1) {
                    certChain.add(certs[j]);
                    j++;
                }
                i = j;
                CertPath certPath = factory.generateCertPath(certChain);
                signers.add(new CodeSigner(certPath, null));
            }
            if (signers.isEmpty()) {
                return null;
            } else {
                return (CodeSigner[])(CodeSigner[])signers.toArray(new CodeSigner[signers.size()]);
            }
        } catch (CertificateException e) {
            return null;
        }
    }
}
