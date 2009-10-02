package java.security.cert;

public interface CRLSelector extends Cloneable {
    
    boolean match(CRL crl);
    
    Object clone();
}
