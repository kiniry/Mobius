package java.security;

import java.security.spec.AlgorithmParameterSpec;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.io.*;
import java.security.cert.Certificate;
import java.security.cert.X509Certificate;
import java.nio.ByteBuffer;
import java.security.Provider.Service;
import javax.crypto.Cipher;
import sun.security.util.Debug;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

public abstract class Signature extends SignatureSpi {
    
    /*synthetic*/ static boolean access$200(Provider$Service x0) {
        return isSpi(x0);
    }
    
    /*synthetic*/ static Debug access$100() {
        return debug;
    }
    
    /*synthetic*/ static String access$000(Signature x0) {
        return x0.algorithm;
    }
    private static final Debug debug = Debug.getInstance("jca", "Signature");
    private String algorithm;
    Provider provider;
    protected static final int UNINITIALIZED = 0;
    protected static final int SIGN = 2;
    protected static final int VERIFY = 3;
    protected int state = UNINITIALIZED;
    
    protected Signature(String algorithm) {
        
        this.algorithm = algorithm;
    }
    private static final String RSA_SIGNATURE = "NONEwithRSA";
    private static final String RSA_CIPHER = "RSA/ECB/PKCS1Padding";
    private static final List rsaIds = Arrays.asList(new ServiceId[]{new ServiceId("Signature", "NONEwithRSA"), new ServiceId("Cipher", "RSA/ECB/PKCS1Padding"), new ServiceId("Cipher", "RSA/ECB"), new ServiceId("Cipher", "RSA//PKCS1Padding"), new ServiceId("Cipher", "RSA")});
    
    public static Signature getInstance(String algorithm) throws NoSuchAlgorithmException {
        List list;
        if (algorithm.equalsIgnoreCase(RSA_SIGNATURE)) {
            list = GetInstance.getServices(rsaIds);
        } else {
            list = GetInstance.getServices("Signature", algorithm);
        }
        Iterator t = list.iterator();
        if (t.hasNext() == false) {
            throw new NoSuchAlgorithmException(algorithm + " Signature not available");
        }
        NoSuchAlgorithmException failure;
        do {
            Provider$Service s = (Provider$Service)(Provider$Service)t.next();
            if (isSpi(s)) {
                return new Signature$Delegate(s, t, algorithm);
            } else {
                try {
                    GetInstance$Instance instance = GetInstance.getInstance(s, SignatureSpi.class);
                    return getInstance(instance, algorithm);
                } catch (NoSuchAlgorithmException e) {
                    failure = e;
                }
            }
        }         while (t.hasNext());
        throw failure;
    }
    
    private static Signature getInstance(GetInstance$Instance instance, String algorithm) {
        Signature sig;
        if (instance.impl instanceof Signature) {
            sig = (Signature)(Signature)instance.impl;
        } else {
            SignatureSpi spi = (SignatureSpi)(SignatureSpi)instance.impl;
            sig = new Signature$Delegate(spi, algorithm);
        }
        sig.provider = instance.provider;
        return sig;
    }
    private static final Map signatureInfo;
    static {
        signatureInfo = new ConcurrentHashMap();
        Boolean TRUE = Boolean.TRUE;
        signatureInfo.put("sun.security.provider.DSA$RawDSA", TRUE);
        signatureInfo.put("sun.security.provider.DSA$SHA1withDSA", TRUE);
        signatureInfo.put("sun.security.rsa.RSASignature$MD2withRSA", TRUE);
        signatureInfo.put("sun.security.rsa.RSASignature$MD5withRSA", TRUE);
        signatureInfo.put("sun.security.rsa.RSASignature$SHA1withRSA", TRUE);
        signatureInfo.put("sun.security.rsa.RSASignature$SHA256withRSA", TRUE);
        signatureInfo.put("sun.security.rsa.RSASignature$SHA384withRSA", TRUE);
        signatureInfo.put("sun.security.rsa.RSASignature$SHA512withRSA", TRUE);
        signatureInfo.put("com.sun.net.ssl.internal.ssl.RSASignature", TRUE);
        signatureInfo.put("sun.security.pkcs11.P11Signature", TRUE);
    }
    
    private static boolean isSpi(Provider$Service s) {
        if (s.getType().equals("Cipher")) {
            return true;
        }
        String className = s.getClassName();
        Boolean result = (Boolean)signatureInfo.get(className);
        if (result == null) {
            try {
                Object instance = s.newInstance(null);
                boolean r = (instance instanceof SignatureSpi) && (instance instanceof Signature == false);
                if ((debug != null) && (r == false)) {
                    debug.println("Not a SignatureSpi " + className);
                    debug.println("Delayed provider selection may not be " + "available for algorithm " + s.getAlgorithm());
                }
                result = Boolean.valueOf(r);
                signatureInfo.put(className, result);
            } catch (Exception e) {
                return false;
            }
        }
        return result.booleanValue();
    }
    
    public static Signature getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        if (algorithm.equalsIgnoreCase(RSA_SIGNATURE)) {
            if ((provider == null) || (provider.length() == 0)) {
                throw new IllegalArgumentException("missing provider");
            }
            Provider p = Security.getProvider(provider);
            if (p == null) {
                throw new NoSuchProviderException("no such provider: " + provider);
            }
            return getInstanceRSA(p);
        }
        GetInstance$Instance instance = GetInstance.getInstance("Signature", SignatureSpi.class, algorithm, provider);
        return getInstance(instance, algorithm);
    }
    
    public static Signature getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        if (algorithm.equalsIgnoreCase(RSA_SIGNATURE)) {
            if (provider == null) {
                throw new IllegalArgumentException("missing provider");
            }
            return getInstanceRSA(provider);
        }
        GetInstance$Instance instance = GetInstance.getInstance("Signature", SignatureSpi.class, algorithm, provider);
        return getInstance(instance, algorithm);
    }
    
    private static Signature getInstanceRSA(Provider p) throws NoSuchAlgorithmException {
        Provider$Service s = p.getService("Signature", RSA_SIGNATURE);
        if (s != null) {
            GetInstance$Instance instance = GetInstance.getInstance(s, SignatureSpi.class);
            return getInstance(instance, RSA_SIGNATURE);
        }
        try {
            Cipher c = Cipher.getInstance(RSA_CIPHER, p);
            return new Signature$Delegate(new Signature$CipherAdapter(c), RSA_SIGNATURE);
        } catch (GeneralSecurityException e) {
            throw new NoSuchAlgorithmException("no such algorithm: " + RSA_SIGNATURE + " for provider " + p.getName(), e);
        }
    }
    
    public final Provider getProvider() {
        chooseFirstProvider();
        return this.provider;
    }
    
    void chooseFirstProvider() {
    }
    
    public final void initVerify(PublicKey publicKey) throws InvalidKeyException {
        engineInitVerify(publicKey);
        state = VERIFY;
    }
    
    public final void initVerify(Certificate certificate) throws InvalidKeyException {
        if (certificate instanceof java.security.cert.X509Certificate) {
            X509Certificate cert = (X509Certificate)(X509Certificate)certificate;
            Set critSet = cert.getCriticalExtensionOIDs();
            if (critSet != null && !critSet.isEmpty() && critSet.contains("2.5.29.15")) {
                boolean[] keyUsageInfo = cert.getKeyUsage();
                if ((keyUsageInfo != null) && (keyUsageInfo[0] == false)) throw new InvalidKeyException("Wrong key usage");
            }
        }
        PublicKey publicKey = certificate.getPublicKey();
        engineInitVerify(publicKey);
        state = VERIFY;
    }
    
    public final void initSign(PrivateKey privateKey) throws InvalidKeyException {
        engineInitSign(privateKey);
        state = SIGN;
    }
    
    public final void initSign(PrivateKey privateKey, SecureRandom random) throws InvalidKeyException {
        engineInitSign(privateKey, random);
        state = SIGN;
    }
    
    public final byte[] sign() throws SignatureException {
        if (state == SIGN) {
            return engineSign();
        }
        throw new SignatureException("object not initialized for signing");
    }
    
    public final int sign(byte[] outbuf, int offset, int len) throws SignatureException {
        if (outbuf == null) {
            throw new IllegalArgumentException("No output buffer given");
        }
        if (outbuf.length - offset < len) {
            throw new IllegalArgumentException("Output buffer too small for specified offset and length");
        }
        if (state != SIGN) {
            throw new SignatureException("object not initialized for signing");
        }
        return engineSign(outbuf, offset, len);
    }
    
    public final boolean verify(byte[] signature) throws SignatureException {
        if (state == VERIFY) {
            return engineVerify(signature);
        }
        throw new SignatureException("object not initialized for verification");
    }
    
    public final boolean verify(byte[] signature, int offset, int length) throws SignatureException {
        if (state == VERIFY) {
            if ((signature == null) || (offset < 0) || (length < 0) || (offset + length > signature.length)) {
                throw new IllegalArgumentException("Bad arguments");
            }
            return engineVerify(signature, offset, length);
        }
        throw new SignatureException("object not initialized for verification");
    }
    
    public final void update(byte b) throws SignatureException {
        if (state == VERIFY || state == SIGN) {
            engineUpdate(b);
        } else {
            throw new SignatureException("object not initialized for signature or verification");
        }
    }
    
    public final void update(byte[] data) throws SignatureException {
        update(data, 0, data.length);
    }
    
    public final void update(byte[] data, int off, int len) throws SignatureException {
        if (state == SIGN || state == VERIFY) {
            engineUpdate(data, off, len);
        } else {
            throw new SignatureException("object not initialized for signature or verification");
        }
    }
    
    public final void update(ByteBuffer data) throws SignatureException {
        if ((state != SIGN) && (state != VERIFY)) {
            throw new SignatureException("object not initialized for signature or verification");
        }
        if (data == null) {
            throw new NullPointerException();
        }
        engineUpdate(data);
    }
    
    public final String getAlgorithm() {
        return this.algorithm;
    }
    
    public String toString() {
        String initState = "";
        switch (state) {
        case UNINITIALIZED: 
            initState = "<not initialized>";
            break;
        
        case VERIFY: 
            initState = "<initialized for verifying>";
            break;
        
        case SIGN: 
            initState = "<initialized for signing>";
            break;
        
        }
        return "Signature object: " + getAlgorithm() + initState;
    }
    
    
    public final void setParameter(String param, Object value) throws InvalidParameterException {
        engineSetParameter(param, value);
    }
    
    public final void setParameter(AlgorithmParameterSpec params) throws InvalidAlgorithmParameterException {
        engineSetParameter(params);
    }
    
    public final AlgorithmParameters getParameters() {
        return engineGetParameters();
    }
    
    
    public final Object getParameter(String param) throws InvalidParameterException {
        return engineGetParameter(param);
    }
    
    public Object clone() throws CloneNotSupportedException {
        if (this instanceof Cloneable) {
            return super.clone();
        } else {
            throw new CloneNotSupportedException();
        }
    }
    {
    }
    {
    }
}
