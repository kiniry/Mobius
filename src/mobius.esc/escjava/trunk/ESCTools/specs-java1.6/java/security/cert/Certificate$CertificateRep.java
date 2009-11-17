package java.security.cert;

public class Certificate$CertificateRep implements java.io.Serializable {
    private static final long serialVersionUID = -8563758940495660020L;
    private String type;
    private byte[] data;
    
    protected Certificate$CertificateRep(String type, byte[] data) {
        
        this.type = type;
        this.data = data;
    }
    
    protected Object readResolve() throws java.io.ObjectStreamException {
        try {
            CertificateFactory cf = CertificateFactory.getInstance(type);
            return cf.generateCertificate(new java.io.ByteArrayInputStream(data));
        } catch (CertificateException e) {
            throw new java.io.NotSerializableException("java.security.cert.Certificate: " + type + ": " + e.getMessage());
        }
    }
}
