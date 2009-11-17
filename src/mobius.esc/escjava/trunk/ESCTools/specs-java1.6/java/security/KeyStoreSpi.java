package java.security;

import java.io.*;
import java.util.*;
import java.security.KeyStore.*;
import java.security.cert.Certificate;
import java.security.cert.CertificateException;
import javax.crypto.SecretKey;
import javax.security.auth.callback.*;

public abstract class KeyStoreSpi {
    
    public KeyStoreSpi() {
        
    }
    
    public abstract Key engineGetKey(String alias, char[] password) throws NoSuchAlgorithmException, UnrecoverableKeyException;
    
    public abstract Certificate[] engineGetCertificateChain(String alias);
    
    public abstract Certificate engineGetCertificate(String alias);
    
    public abstract Date engineGetCreationDate(String alias);
    
    public abstract void engineSetKeyEntry(String alias, Key key, char[] password, Certificate[] chain) throws KeyStoreException;
    
    public abstract void engineSetKeyEntry(String alias, byte[] key, Certificate[] chain) throws KeyStoreException;
    
    public abstract void engineSetCertificateEntry(String alias, Certificate cert) throws KeyStoreException;
    
    public abstract void engineDeleteEntry(String alias) throws KeyStoreException;
    
    public abstract Enumeration engineAliases();
    
    public abstract boolean engineContainsAlias(String alias);
    
    public abstract int engineSize();
    
    public abstract boolean engineIsKeyEntry(String alias);
    
    public abstract boolean engineIsCertificateEntry(String alias);
    
    public abstract String engineGetCertificateAlias(Certificate cert);
    
    public abstract void engineStore(OutputStream stream, char[] password) throws IOException, NoSuchAlgorithmException, CertificateException;
    
    public void engineStore(KeyStore$LoadStoreParameter param) throws IOException, NoSuchAlgorithmException, CertificateException {
        throw new UnsupportedOperationException();
    }
    
    public abstract void engineLoad(InputStream stream, char[] password) throws IOException, NoSuchAlgorithmException, CertificateException;
    
    public void engineLoad(KeyStore$LoadStoreParameter param) throws IOException, NoSuchAlgorithmException, CertificateException {
        if (param == null) {
            engineLoad((InputStream)null, (char[])null);
            return;
        }
        if (param instanceof KeyStore$SimpleLoadStoreParameter) {
            KeyStore$ProtectionParameter protection = param.getProtectionParameter();
            char[] password;
            if (protection instanceof KeyStore$PasswordProtection) {
                password = ((KeyStore$PasswordProtection)(KeyStore$PasswordProtection)param).getPassword();
            } else if (protection instanceof KeyStore$CallbackHandlerProtection) {
                CallbackHandler handler = ((KeyStore$CallbackHandlerProtection)(KeyStore$CallbackHandlerProtection)param).getCallbackHandler();
                PasswordCallback callback = new PasswordCallback("Password: ", false);
                try {
                    handler.handle(new Callback[]{callback});
                } catch (UnsupportedCallbackException e) {
                    throw new NoSuchAlgorithmException("Could not obtain password", e);
                }
                password = callback.getPassword();
                callback.clearPassword();
                if (password == null) {
                    throw new NoSuchAlgorithmException("No password provided");
                }
            } else {
                throw new NoSuchAlgorithmException("ProtectionParameter must be PasswordProtection or CallbackHandlerProtection");
            }
            engineLoad(null, password);
            return;
        }
        throw new UnsupportedOperationException();
    }
    
    public KeyStore$Entry engineGetEntry(String alias, KeyStore$ProtectionParameter protParam) throws KeyStoreException, NoSuchAlgorithmException, UnrecoverableEntryException {
        if (!engineContainsAlias(alias)) {
            return null;
        }
        if (protParam == null) {
            if (engineIsCertificateEntry(alias)) {
                return new KeyStore$TrustedCertificateEntry(engineGetCertificate(alias));
            } else {
                throw new UnrecoverableEntryException("requested entry requires a password");
            }
        }
        if (protParam instanceof KeyStore$PasswordProtection) {
            if (engineIsCertificateEntry(alias)) {
                throw new UnsupportedOperationException("trusted certificate entries are not password-protected");
            } else if (engineIsKeyEntry(alias)) {
                KeyStore$PasswordProtection pp = (KeyStore$PasswordProtection)(KeyStore$PasswordProtection)protParam;
                char[] password = pp.getPassword();
                try {
                    Key key = engineGetKey(alias, password);
                    if (key instanceof PrivateKey) {
                        Certificate[] chain = engineGetCertificateChain(alias);
                        return new KeyStore$PrivateKeyEntry((PrivateKey)(PrivateKey)key, chain);
                    } else if (key instanceof SecretKey) {
                        return new KeyStore$SecretKeyEntry((SecretKey)(SecretKey)key);
                    }
                } catch (UnrecoverableKeyException uke) {
                    UnrecoverableEntryException uee = new UnrecoverableEntryException();
                    uee.initCause(uke);
                    throw uee;
                }
            }
        }
        throw new UnsupportedOperationException();
    }
    
    public void engineSetEntry(String alias, KeyStore$Entry entry, KeyStore$ProtectionParameter protParam) throws KeyStoreException {
        if (protParam != null && !(protParam instanceof KeyStore$PasswordProtection)) {
            throw new KeyStoreException("unsupported protection parameter");
        }
        KeyStore$PasswordProtection pProtect = null;
        if (protParam != null) {
            pProtect = (KeyStore$PasswordProtection)(KeyStore$PasswordProtection)protParam;
        }
        if (entry instanceof KeyStore$TrustedCertificateEntry) {
            if (protParam != null && pProtect.getPassword() != null) {
                throw new KeyStoreException("trusted certificate entries are not password-protected");
            } else {
                KeyStore$TrustedCertificateEntry tce = (KeyStore$TrustedCertificateEntry)(KeyStore$TrustedCertificateEntry)entry;
                engineSetCertificateEntry(alias, tce.getTrustedCertificate());
                return;
            }
        } else if (entry instanceof KeyStore$PrivateKeyEntry) {
            if (pProtect == null || pProtect.getPassword() == null) {
                throw new KeyStoreException("non-null password required to create PrivateKeyEntry");
            } else {
                engineSetKeyEntry(alias, ((KeyStore$PrivateKeyEntry)(KeyStore$PrivateKeyEntry)entry).getPrivateKey(), pProtect.getPassword(), ((KeyStore$PrivateKeyEntry)(KeyStore$PrivateKeyEntry)entry).getCertificateChain());
                return;
            }
        } else if (entry instanceof KeyStore$SecretKeyEntry) {
            if (pProtect == null || pProtect.getPassword() == null) {
                throw new KeyStoreException("non-null password required to create SecretKeyEntry");
            } else {
                engineSetKeyEntry(alias, ((KeyStore$SecretKeyEntry)(KeyStore$SecretKeyEntry)entry).getSecretKey(), pProtect.getPassword(), (Certificate[])null);
                return;
            }
        }
        throw new KeyStoreException("unsupported entry type: " + entry.getClass().getName());
    }
    
    public boolean engineEntryInstanceOf(String alias, Class entryClass) {
        if (entryClass == TrustedCertificateEntry.class) {
            return engineIsCertificateEntry(alias);
        }
        if (entryClass == PrivateKeyEntry.class) {
            return engineIsKeyEntry(alias) && engineGetCertificate(alias) != null;
        }
        if (entryClass == SecretKeyEntry.class) {
            return engineIsKeyEntry(alias) && engineGetCertificate(alias) == null;
        }
        return false;
    }
}
