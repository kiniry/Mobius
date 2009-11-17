package java.security.cert;

import java.math.BigInteger;
import java.util.Date;
import javax.security.auth.x500.X500Principal;

public abstract class X509CRLEntry implements X509Extension {
    
    public X509CRLEntry() {
        
    }
    
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof X509CRLEntry)) return false;
        try {
            byte[] thisCRLEntry = this.getEncoded();
            byte[] otherCRLEntry = ((X509CRLEntry)(X509CRLEntry)other).getEncoded();
            if (thisCRLEntry.length != otherCRLEntry.length) return false;
            for (int i = 0; i < thisCRLEntry.length; i++) if (thisCRLEntry[i] != otherCRLEntry[i]) return false;
        } catch (CRLException ce) {
            return false;
        }
        return true;
    }
    
    public int hashCode() {
        int retval = 0;
        try {
            byte[] entryData = this.getEncoded();
            for (int i = 1; i < entryData.length; i++) retval += entryData[i] * i;
        } catch (CRLException ce) {
            return (retval);
        }
        return (retval);
    }
    
    public abstract byte[] getEncoded() throws CRLException;
    
    public abstract BigInteger getSerialNumber();
    
    public X500Principal getCertificateIssuer() {
        return null;
    }
    
    public abstract Date getRevocationDate();
    
    public abstract boolean hasExtensions();
    
    public abstract String toString();
}
