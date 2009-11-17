package java.security;

import java.io.Serializable;
import java.security.cert.CertPath;
import java.util.Date;

public final class Timestamp implements Serializable {
    private static final long serialVersionUID = -5502683707821851294L;
    private Date timestamp;
    private CertPath signerCertPath;
    private transient int myhash = -1;
    
    public Timestamp(Date timestamp, CertPath signerCertPath) {
        
        if (timestamp == null || signerCertPath == null) {
            throw new NullPointerException();
        }
        this.timestamp = new Date(timestamp.getTime());
        this.signerCertPath = signerCertPath;
    }
    
    public Date getTimestamp() {
        return new Date(timestamp.getTime());
    }
    
    public CertPath getSignerCertPath() {
        return signerCertPath;
    }
    
    public int hashCode() {
        if (myhash == -1) {
            myhash = timestamp.hashCode() + signerCertPath.hashCode();
        }
        return myhash;
    }
    
    public boolean equals(Object obj) {
        if (obj == null || (!(obj instanceof Timestamp))) {
            return false;
        }
        Timestamp that = (Timestamp)(Timestamp)obj;
        if (this == that) {
            return true;
        }
        return (timestamp.equals(that.getTimestamp()) && signerCertPath.equals(that.getSignerCertPath()));
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("(");
        sb.append("timestamp: " + timestamp);
        sb.append("TSA: " + signerCertPath.getCertificates().get(0));
        sb.append(")");
        return sb.toString();
    }
}
