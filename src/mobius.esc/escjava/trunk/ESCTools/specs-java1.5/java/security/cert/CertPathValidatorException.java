package java.security.cert;

import java.security.GeneralSecurityException;

public class CertPathValidatorException extends GeneralSecurityException {
    private static final long serialVersionUID = -3083180014971893139L;
    private int index = -1;
    private CertPath certPath;
    
    public CertPathValidatorException() {
        
    }
    
    public CertPathValidatorException(String msg) {
        super(msg);
    }
    
    public CertPathValidatorException(Throwable cause) {
        super(cause);
    }
    
    public CertPathValidatorException(String msg, Throwable cause) {
        super(msg, cause);
    }
    
    public CertPathValidatorException(String msg, Throwable cause, CertPath certPath, int index) {
        super(msg, cause);
        if (certPath == null && index != -1) {
            throw new IllegalArgumentException();
        }
        if (index < -1 || (certPath != null && index >= certPath.getCertificates().size())) {
            throw new IndexOutOfBoundsException();
        }
        this.certPath = certPath;
        this.index = index;
    }
    
    public CertPath getCertPath() {
        return this.certPath;
    }
    
    public int getIndex() {
        return this.index;
    }
}
