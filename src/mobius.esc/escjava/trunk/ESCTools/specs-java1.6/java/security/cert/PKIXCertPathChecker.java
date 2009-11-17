package java.security.cert;

import java.util.Collection;
import java.util.Set;

public abstract class PKIXCertPathChecker implements Cloneable {
    
    protected PKIXCertPathChecker() {
        
    }
    
    public abstract void init(boolean forward) throws CertPathValidatorException;
    
    public abstract boolean isForwardCheckingSupported();
    
    public abstract Set getSupportedExtensions();
    
    public abstract void check(Certificate cert, Collection unresolvedCritExts) throws CertPathValidatorException;
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e.toString());
        }
    }
}
