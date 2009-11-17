package java.security.cert;

import java.io.NotSerializableException;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.util.Iterator;
import java.util.List;

public abstract class CertPath implements Serializable {
    private static final long serialVersionUID = 6068470306649138683L;
    private String type;
    
    protected CertPath(String type) {
        
        this.type = type;
    }
    
    public String getType() {
        return type;
    }
    
    public abstract Iterator getEncodings();
    
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof CertPath)) return false;
        CertPath otherCP = (CertPath)(CertPath)other;
        if (!otherCP.getType().equals(type)) return false;
        List thisCertList = this.getCertificates();
        List otherCertList = otherCP.getCertificates();
        return (thisCertList.equals(otherCertList));
    }
    
    public int hashCode() {
        int hashCode = type.hashCode();
        hashCode = 31 * hashCode + getCertificates().hashCode();
        return hashCode;
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        Iterator stringIterator = getCertificates().iterator();
        sb.append("\n" + type + " Cert Path: length = " + getCertificates().size() + ".\n");
        sb.append("[\n");
        int i = 1;
        while (stringIterator.hasNext()) {
            sb.append("==========================================" + "===============Certificate " + i + " start.\n");
            Certificate stringCert = (Certificate)(Certificate)stringIterator.next();
            sb.append(stringCert.toString());
            sb.append("\n========================================" + "=================Certificate " + i + " end.\n\n\n");
            i++;
        }
        sb.append("\n]");
        return sb.toString();
    }
    
    public abstract byte[] getEncoded() throws CertificateEncodingException;
    
    public abstract byte[] getEncoded(String encoding) throws CertificateEncodingException;
    
    public abstract List getCertificates();
    
    protected Object writeReplace() throws ObjectStreamException {
        try {
            return new CertPath$CertPathRep(type, getEncoded());
        } catch (CertificateException ce) {
            NotSerializableException nse = new NotSerializableException("java.security.cert.CertPath: " + type);
            nse.initCause(ce);
            throw nse;
        }
    }
    {
    }
}
