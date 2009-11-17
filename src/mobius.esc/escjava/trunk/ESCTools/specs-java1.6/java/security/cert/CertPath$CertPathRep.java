package java.security.cert;

import java.io.ByteArrayInputStream;
import java.io.NotSerializableException;
import java.io.ObjectStreamException;
import java.io.Serializable;

public class CertPath$CertPathRep implements Serializable {
    private static final long serialVersionUID = 3015633072427920915L;
    private String type;
    private byte[] data;
    
    protected CertPath$CertPathRep(String type, byte[] data) {
        
        this.type = type;
        this.data = data;
    }
    
    protected Object readResolve() throws ObjectStreamException {
        try {
            CertificateFactory cf = CertificateFactory.getInstance(type);
            return cf.generateCertPath(new ByteArrayInputStream(data));
        } catch (CertificateException ce) {
            NotSerializableException nse = new NotSerializableException("java.security.cert.CertPath: " + type);
            nse.initCause(ce);
            throw nse;
        }
    }
}
