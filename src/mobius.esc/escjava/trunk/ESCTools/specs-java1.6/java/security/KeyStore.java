package java.security;

import java.io.*;
import java.security.cert.Certificate;
import java.security.cert.CertificateException;
import java.util.*;
import javax.security.auth.callback.*;

public class KeyStore {
    
    /*synthetic*/ static boolean access$000(KeyStore x0) {
        return x0.initialized;
    }
    private static final String KEYSTORE_TYPE = "keystore.type";
    private String type;
    private Provider provider;
    private KeyStoreSpi keyStoreSpi;
    private boolean initialized = false;
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    protected KeyStore(KeyStoreSpi keyStoreSpi, Provider provider, String type) {
        
        this.keyStoreSpi = keyStoreSpi;
        this.provider = provider;
        this.type = type;
    }
    
    public static KeyStore getInstance(String type) throws KeyStoreException {
        try {
            Object[] objs = Security.getImpl(type, "KeyStore", (String)null);
            return new KeyStore((KeyStoreSpi)(KeyStoreSpi)objs[0], (Provider)(Provider)objs[1], type);
        } catch (NoSuchAlgorithmException nsae) {
            throw new KeyStoreException(type + " not found");
        } catch (NoSuchProviderException nspe) {
            throw new KeyStoreException(type + " not found");
        }
    }
    
    public static KeyStore getInstance(String type, String provider) throws KeyStoreException, NoSuchProviderException {
        if (provider == null || provider.length() == 0) throw new IllegalArgumentException("missing provider");
        try {
            Object[] objs = Security.getImpl(type, "KeyStore", provider);
            return new KeyStore((KeyStoreSpi)(KeyStoreSpi)objs[0], (Provider)(Provider)objs[1], type);
        } catch (NoSuchAlgorithmException nsae) {
            throw new KeyStoreException(type + " not found");
        }
    }
    
    public static KeyStore getInstance(String type, Provider provider) throws KeyStoreException {
        if (provider == null) throw new IllegalArgumentException("missing provider");
        try {
            Object[] objs = Security.getImpl(type, "KeyStore", provider);
            return new KeyStore((KeyStoreSpi)(KeyStoreSpi)objs[0], (Provider)(Provider)objs[1], type);
        } catch (NoSuchAlgorithmException nsae) {
            throw new KeyStoreException(type + " not found");
        }
    }
    
    public static final String getDefaultType() {
        String kstype;
        kstype = (String)(String)AccessController.doPrivileged(new KeyStore$1());
        if (kstype == null) {
            kstype = "jks";
        }
        return kstype;
    }
    
    public final Provider getProvider() {
        return this.provider;
    }
    
    public final String getType() {
        return this.type;
    }
    
    public final Key getKey(String alias, char[] password) throws KeyStoreException, NoSuchAlgorithmException, UnrecoverableKeyException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineGetKey(alias, password);
    }
    
    public final Certificate[] getCertificateChain(String alias) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineGetCertificateChain(alias);
    }
    
    public final Certificate getCertificate(String alias) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineGetCertificate(alias);
    }
    
    public final Date getCreationDate(String alias) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineGetCreationDate(alias);
    }
    
    public final void setKeyEntry(String alias, Key key, char[] password, Certificate[] chain) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        if ((key instanceof PrivateKey) && (chain == null || chain.length == 0)) {
            throw new IllegalArgumentException("Private key must be accompanied by certificate chain");
        }
        keyStoreSpi.engineSetKeyEntry(alias, key, password, chain);
    }
    
    public final void setKeyEntry(String alias, byte[] key, Certificate[] chain) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        keyStoreSpi.engineSetKeyEntry(alias, key, chain);
    }
    
    public final void setCertificateEntry(String alias, Certificate cert) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        keyStoreSpi.engineSetCertificateEntry(alias, cert);
    }
    
    public final void deleteEntry(String alias) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        keyStoreSpi.engineDeleteEntry(alias);
    }
    
    public final Enumeration aliases() throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineAliases();
    }
    
    public final boolean containsAlias(String alias) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineContainsAlias(alias);
    }
    
    public final int size() throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineSize();
    }
    
    public final boolean isKeyEntry(String alias) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineIsKeyEntry(alias);
    }
    
    public final boolean isCertificateEntry(String alias) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineIsCertificateEntry(alias);
    }
    
    public final String getCertificateAlias(Certificate cert) throws KeyStoreException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineGetCertificateAlias(cert);
    }
    
    public final void store(OutputStream stream, char[] password) throws KeyStoreException, IOException, NoSuchAlgorithmException, CertificateException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        keyStoreSpi.engineStore(stream, password);
    }
    
    public final void store(KeyStore$LoadStoreParameter param) throws KeyStoreException, IOException, NoSuchAlgorithmException, CertificateException {
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        keyStoreSpi.engineStore(param);
    }
    
    public final void load(InputStream stream, char[] password) throws IOException, NoSuchAlgorithmException, CertificateException {
        keyStoreSpi.engineLoad(stream, password);
        initialized = true;
    }
    
    public final void load(KeyStore$LoadStoreParameter param) throws IOException, NoSuchAlgorithmException, CertificateException {
        keyStoreSpi.engineLoad(param);
        initialized = true;
    }
    
    public final KeyStore$Entry getEntry(String alias, KeyStore$ProtectionParameter protParam) throws NoSuchAlgorithmException, UnrecoverableEntryException, KeyStoreException {
        if (alias == null) {
            throw new NullPointerException("invalid null input");
        }
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineGetEntry(alias, protParam);
    }
    
    public final void setEntry(String alias, KeyStore$Entry entry, KeyStore$ProtectionParameter protParam) throws KeyStoreException {
        if (alias == null || entry == null) {
            throw new NullPointerException("invalid null input");
        }
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        keyStoreSpi.engineSetEntry(alias, entry, protParam);
    }
    
    public final boolean entryInstanceOf(String alias, Class entryClass) throws KeyStoreException {
        if (alias == null || entryClass == null) {
            throw new NullPointerException("invalid null input");
        }
        if (!initialized) {
            throw new KeyStoreException("Uninitialized keystore");
        }
        return keyStoreSpi.engineEntryInstanceOf(alias, entryClass);
    }
    {
    }
    {
    }
}
