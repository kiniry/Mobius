package java.security.cert;

public interface CertSelector extends Cloneable {
    
    boolean match(Certificate cert);
    
    Object clone();
}
