package java.security;

import java.util.*;
import java.security.Provider.Service;
import sun.security.jca.*;
import sun.security.jca.GetInstance.Instance;

public class SecureRandom extends java.util.Random {
    private Provider provider = null;
    private SecureRandomSpi secureRandomSpi = null;
    private String algorithm;
    private static SecureRandom seedGenerator = null;
    
    public SecureRandom() {
        super(0);
        getDefaultPRNG(false, null);
    }
    
    public SecureRandom(byte[] seed) {
        super(0);
        getDefaultPRNG(true, seed);
    }
    
    private void getDefaultPRNG(boolean setSeed, byte[] seed) {
        String prng = getPrngAlgorithm();
        if (prng == null) {
            prng = "SHA1PRNG";
            this.secureRandomSpi = new sun.security.provider.SecureRandom();
            this.provider = new sun.security.provider.Sun();
            if (setSeed) {
                this.secureRandomSpi.engineSetSeed(seed);
            }
        } else {
            try {
                SecureRandom random = SecureRandom.getInstance(prng);
                this.secureRandomSpi = random.getSecureRandomSpi();
                this.provider = random.getProvider();
                if (setSeed) {
                    this.secureRandomSpi.engineSetSeed(seed);
                }
            } catch (NoSuchAlgorithmException nsae) {
            }
        }
        if (getClass() == SecureRandom.class) {
            this.algorithm = prng;
        }
    }
    
    protected SecureRandom(SecureRandomSpi secureRandomSpi, Provider provider) {
        this(secureRandomSpi, provider, null);
    }
    
    private SecureRandom(SecureRandomSpi secureRandomSpi, Provider provider, String algorithm) {
        super(0);
        this.secureRandomSpi = secureRandomSpi;
        this.provider = provider;
        this.algorithm = algorithm;
    }
    
    public static SecureRandom getInstance(String algorithm) throws NoSuchAlgorithmException {
        GetInstance$Instance instance = GetInstance.getInstance("SecureRandom", SecureRandomSpi.class, algorithm);
        return new SecureRandom((SecureRandomSpi)(SecureRandomSpi)instance.impl, instance.provider, algorithm);
    }
    
    public static SecureRandom getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        GetInstance$Instance instance = GetInstance.getInstance("SecureRandom", SecureRandomSpi.class, algorithm, provider);
        return new SecureRandom((SecureRandomSpi)(SecureRandomSpi)instance.impl, instance.provider, algorithm);
    }
    
    public static SecureRandom getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        GetInstance$Instance instance = GetInstance.getInstance("SecureRandom", SecureRandomSpi.class, algorithm, provider);
        return new SecureRandom((SecureRandomSpi)(SecureRandomSpi)instance.impl, instance.provider, algorithm);
    }
    
    SecureRandomSpi getSecureRandomSpi() {
        return secureRandomSpi;
    }
    
    public final Provider getProvider() {
        return provider;
    }
    
    public String getAlgorithm() {
        return (algorithm != null) ? algorithm : "unknown";
    }
    
    public synchronized void setSeed(byte[] seed) {
        secureRandomSpi.engineSetSeed(seed);
    }
    
    public void setSeed(long seed) {
        if (seed != 0) {
            secureRandomSpi.engineSetSeed(longToByteArray(seed));
        }
    }
    
    public synchronized void nextBytes(byte[] bytes) {
        secureRandomSpi.engineNextBytes(bytes);
    }
    
    protected final int next(int numBits) {
        int numBytes = (numBits + 7) / 8;
        byte[] b = new byte[numBytes];
        int next = 0;
        nextBytes(b);
        for (int i = 0; i < numBytes; i++) next = (next << 8) + (b[i] & 255);
        return next >>> (numBytes * 8 - numBits);
    }
    
    public static byte[] getSeed(int numBytes) {
        if (seedGenerator == null) seedGenerator = new SecureRandom();
        return seedGenerator.generateSeed(numBytes);
    }
    
    public byte[] generateSeed(int numBytes) {
        return secureRandomSpi.engineGenerateSeed(numBytes);
    }
    
    private static byte[] longToByteArray(long l) {
        byte[] retVal = new byte[8];
        for (int i = 0; i < 8; i++) {
            retVal[i] = (byte)l;
            l >>= 8;
        }
        return retVal;
    }
    
    private static String getPrngAlgorithm() {
        List provs = Providers.getProviderList().providers();
        for (Iterator t = provs.iterator(); t.hasNext(); ) {
            Provider p = (Provider)(Provider)t.next();
            for (Iterator u = p.getServices().iterator(); u.hasNext(); ) {
                Provider$Service s = (Provider$Service)(Provider$Service)u.next();
                if (s.getType().equals("SecureRandom")) {
                    return s.getAlgorithm();
                }
            }
        }
        return null;
    }
    static final long serialVersionUID = 4940670005562187L;
    private byte[] state;
    private MessageDigest digest = null;
    private byte[] randomBytes;
    private int randomBytesUsed;
    private long counter;
}
