package java.security;

import java.io.*;
import java.security.cert.Certificate;
import java.util.*;
import javax.security.auth.callback.*;

public final class KeyStore$TrustedCertificateEntry implements KeyStore$Entry {
    private final Certificate cert;
    
    public KeyStore$TrustedCertificateEntry(Certificate trustedCert) {
        
        if (trustedCert == null) {
            throw new NullPointerException("invalid null input");
        }
        this.cert = trustedCert;
    }
    
    public Certificate getTrustedCertificate() {
        return cert;
    }
    
    public String toString() {
        return "Trusted certificate entry:\r\n" + cert.toString();
    }
}
