package java.security;

import java.io.*;
import java.security.cert.Certificate;
import java.security.cert.X509Certificate;
import java.util.*;
import javax.security.auth.callback.*;

public final class KeyStore$PrivateKeyEntry implements KeyStore$Entry {
    private final PrivateKey privKey;
    private final Certificate[] chain;
    
    public KeyStore$PrivateKeyEntry(PrivateKey privateKey, Certificate[] chain) {
        
        if (privateKey == null || chain == null) {
            throw new NullPointerException("invalid null input");
        }
        if (chain.length == 0) {
            throw new IllegalArgumentException("invalid zero-length input chain");
        }
        Certificate[] clonedChain = (Certificate[])(Certificate[])chain.clone();
        String certType = clonedChain[0].getType();
        for (int i = 1; i < clonedChain.length; i++) {
            if (!certType.equals(clonedChain[i].getType())) {
                throw new IllegalArgumentException("chain does not contain certificates of the same type");
            }
        }
        if (!privateKey.getAlgorithm().equals(clonedChain[0].getPublicKey().getAlgorithm())) {
            throw new IllegalArgumentException("private key algorithm does not match algorithm of public key in end entity certificate (at index 0)");
        }
        this.privKey = privateKey;
        if (clonedChain[0] instanceof X509Certificate && !(clonedChain instanceof X509Certificate[])) {
            this.chain = new X509Certificate[clonedChain.length];
            System.arraycopy(clonedChain, 0, this.chain, 0, clonedChain.length);
        } else {
            this.chain = clonedChain;
        }
    }
    
    public PrivateKey getPrivateKey() {
        return privKey;
    }
    
    public Certificate[] getCertificateChain() {
        return (Certificate[])(Certificate[])chain.clone();
    }
    
    public Certificate getCertificate() {
        return chain[0];
    }
    
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("Private key entry and certificate chain with " + chain.length + " elements:\r\n");
        for (Certificate[] arr$ = chain, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Certificate cert = arr$[i$];
            {
                sb.append(cert);
                sb.append("\r\n");
            }
        }
        return sb.toString();
    }
}
