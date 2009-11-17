package java.security;

import java.security.spec.AlgorithmParameterSpec;
import java.util.*;
import java.io.*;
import java.nio.ByteBuffer;
import java.security.Provider.Service;
import javax.crypto.Cipher;
import javax.crypto.NoSuchPaddingException;
import sun.security.jca.*;

class Signature$Delegate extends Signature {
    private SignatureSpi sigSpi;
    private final Object lock;
    private Provider$Service firstService;
    private Iterator serviceIterator;
    
    Signature$Delegate(SignatureSpi sigSpi, String algorithm) {
        super(algorithm);
        this.sigSpi = sigSpi;
        this.lock = null;
    }
    
    Signature$Delegate(Provider$Service service, Iterator iterator, String algorithm) {
        super(algorithm);
        this.firstService = service;
        this.serviceIterator = iterator;
        this.lock = new Object();
    }
    
    public Object clone() throws CloneNotSupportedException {
        chooseFirstProvider();
        if (sigSpi instanceof Cloneable) {
            SignatureSpi sigSpiClone = (SignatureSpi)(SignatureSpi)sigSpi.clone();
            Signature that = new Signature$Delegate(sigSpiClone, Signature.access$000(((Signature)this)));
            that.provider = ((Signature)this).provider;
            return that;
        } else {
            throw new CloneNotSupportedException();
        }
    }
    
    private static SignatureSpi newInstance(Provider$Service s) throws NoSuchAlgorithmException {
        if (s.getType().equals("Cipher")) {
            try {
                Cipher c = Cipher.getInstance("RSA/ECB/PKCS1Padding", s.getProvider());
                return new Signature$CipherAdapter(c);
            } catch (NoSuchPaddingException e) {
                throw new NoSuchAlgorithmException(e);
            }
        } else {
            Object o = s.newInstance(null);
            if (o instanceof SignatureSpi == false) {
                throw new NoSuchAlgorithmException("Not a SignatureSpi: " + o.getClass().getName());
            }
            return (SignatureSpi)(SignatureSpi)o;
        }
    }
    private static int warnCount = 10;
    
    void chooseFirstProvider() {
        if (sigSpi != null) {
            return;
        }
        synchronized (lock) {
            if (sigSpi != null) {
                return;
            }
            if (Signature.access$100() != null) {
                int w = --warnCount;
                if (w >= 0) {
                    Signature.access$100().println("Signature.init() not first method called, disabling delayed provider selection");
                    if (w == 0) {
                        Signature.access$100().println("Further warnings of this type will be suppressed");
                    }
                    new Exception("Call trace").printStackTrace();
                }
            }
            Exception lastException = null;
            while ((firstService != null) || serviceIterator.hasNext()) {
                Provider$Service s;
                if (firstService != null) {
                    s = firstService;
                    firstService = null;
                } else {
                    s = (Provider$Service)(Provider$Service)serviceIterator.next();
                }
                if (Signature.access$200(s) == false) {
                    continue;
                }
                try {
                    sigSpi = newInstance(s);
                    provider = s.getProvider();
                    firstService = null;
                    serviceIterator = null;
                    return;
                } catch (NoSuchAlgorithmException e) {
                    lastException = e;
                }
            }
            ProviderException e = new ProviderException("Could not construct SignatureSpi instance");
            if (lastException != null) {
                e.initCause(lastException);
            }
            throw e;
        }
    }
    
    private void chooseProvider(int type, Key key, SecureRandom random) throws InvalidKeyException {
        synchronized (lock) {
            if (sigSpi != null) {
                init(sigSpi, type, key, random);
                return;
            }
            Exception lastException = null;
            while ((firstService != null) || serviceIterator.hasNext()) {
                Provider$Service s;
                if (firstService != null) {
                    s = firstService;
                    firstService = null;
                } else {
                    s = (Provider$Service)(Provider$Service)serviceIterator.next();
                }
                if (s.supportsParameter(key) == false) {
                    continue;
                }
                if (Signature.access$200(s) == false) {
                    continue;
                }
                try {
                    SignatureSpi spi = newInstance(s);
                    init(spi, type, key, random);
                    provider = s.getProvider();
                    sigSpi = spi;
                    firstService = null;
                    serviceIterator = null;
                    return;
                } catch (Exception e) {
                    if (lastException == null) {
                        lastException = e;
                    }
                }
            }
            if (lastException instanceof InvalidKeyException) {
                throw (InvalidKeyException)(InvalidKeyException)lastException;
            }
            if (lastException instanceof RuntimeException) {
                throw (RuntimeException)(RuntimeException)lastException;
            }
            String k = (key != null) ? key.getClass().getName() : "(null)";
            throw new InvalidKeyException("No installed provider supports this key: " + k, lastException);
        }
    }
    private static final int I_PUB = 1;
    private static final int I_PRIV = 2;
    private static final int I_PRIV_SR = 3;
    
    private void init(SignatureSpi spi, int type, Key key, SecureRandom random) throws InvalidKeyException {
        switch (type) {
        case I_PUB: 
            spi.engineInitVerify((PublicKey)(PublicKey)key);
            break;
        
        case I_PRIV: 
            spi.engineInitSign((PrivateKey)(PrivateKey)key);
            break;
        
        case I_PRIV_SR: 
            spi.engineInitSign((PrivateKey)(PrivateKey)key, random);
            break;
        
        default: 
            throw new AssertionError("Internal error: " + type);
        
        }
    }
    
    protected void engineInitVerify(PublicKey publicKey) throws InvalidKeyException {
        if (sigSpi != null) {
            sigSpi.engineInitVerify(publicKey);
        } else {
            chooseProvider(I_PUB, publicKey, null);
        }
    }
    
    protected void engineInitSign(PrivateKey privateKey) throws InvalidKeyException {
        if (sigSpi != null) {
            sigSpi.engineInitSign(privateKey);
        } else {
            chooseProvider(I_PRIV, privateKey, null);
        }
    }
    
    protected void engineInitSign(PrivateKey privateKey, SecureRandom sr) throws InvalidKeyException {
        if (sigSpi != null) {
            sigSpi.engineInitSign(privateKey, sr);
        } else {
            chooseProvider(I_PRIV_SR, privateKey, sr);
        }
    }
    
    protected void engineUpdate(byte b) throws SignatureException {
        chooseFirstProvider();
        sigSpi.engineUpdate(b);
    }
    
    protected void engineUpdate(byte[] b, int off, int len) throws SignatureException {
        chooseFirstProvider();
        sigSpi.engineUpdate(b, off, len);
    }
    
    protected void engineUpdate(ByteBuffer data) {
        chooseFirstProvider();
        sigSpi.engineUpdate(data);
    }
    
    protected byte[] engineSign() throws SignatureException {
        chooseFirstProvider();
        return sigSpi.engineSign();
    }
    
    protected int engineSign(byte[] outbuf, int offset, int len) throws SignatureException {
        chooseFirstProvider();
        return sigSpi.engineSign(outbuf, offset, len);
    }
    
    protected boolean engineVerify(byte[] sigBytes) throws SignatureException {
        chooseFirstProvider();
        return sigSpi.engineVerify(sigBytes);
    }
    
    protected boolean engineVerify(byte[] sigBytes, int offset, int length) throws SignatureException {
        chooseFirstProvider();
        return sigSpi.engineVerify(sigBytes, offset, length);
    }
    
    protected void engineSetParameter(String param, Object value) throws InvalidParameterException {
        chooseFirstProvider();
        sigSpi.engineSetParameter(param, value);
    }
    
    protected void engineSetParameter(AlgorithmParameterSpec params) throws InvalidAlgorithmParameterException {
        chooseFirstProvider();
        sigSpi.engineSetParameter(params);
    }
    
    protected Object engineGetParameter(String param) throws InvalidParameterException {
        chooseFirstProvider();
        return sigSpi.engineGetParameter(param);
    }
    
    protected AlgorithmParameters engineGetParameters() {
        chooseFirstProvider();
        return sigSpi.engineGetParameters();
    }
}
