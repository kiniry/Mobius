package java.security;

import java.util.*;
import java.lang.*;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.ByteBuffer;

public abstract class MessageDigest extends MessageDigestSpi {
    
    /*synthetic*/ static int access$202(MessageDigest x0, int x1) {
        return x0.state = x1;
    }
    
    /*synthetic*/ static int access$200(MessageDigest x0) {
        return x0.state;
    }
    
    /*synthetic*/ static Provider access$102(MessageDigest x0, Provider x1) {
        return x0.provider = x1;
    }
    
    /*synthetic*/ static Provider access$100(MessageDigest x0) {
        return x0.provider;
    }
    
    /*synthetic*/ static java.lang.String access$000(MessageDigest x0) {
        return x0.algorithm;
    }
    private String algorithm;
    private static final int INITIAL = 0;
    private static final int IN_PROGRESS = 1;
    private int state = INITIAL;
    private Provider provider;
    
    protected MessageDigest(String algorithm) {
        
        this.algorithm = algorithm;
    }
    
    public static MessageDigest getInstance(String algorithm) throws NoSuchAlgorithmException {
        try {
            Object[] objs = Security.getImpl(algorithm, "MessageDigest", (String)null);
            if (objs[0] instanceof MessageDigest) {
                MessageDigest md = (MessageDigest)(MessageDigest)objs[0];
                md.provider = (Provider)(Provider)objs[1];
                return md;
            } else {
                MessageDigest delegate = new MessageDigest$Delegate((MessageDigestSpi)(MessageDigestSpi)objs[0], algorithm);
                delegate.provider = (Provider)(Provider)objs[1];
                return delegate;
            }
        } catch (NoSuchProviderException e) {
            throw new NoSuchAlgorithmException(algorithm + " not found");
        }
    }
    
    public static MessageDigest getInstance(String algorithm, String provider) throws NoSuchAlgorithmException, NoSuchProviderException {
        if (provider == null || provider.length() == 0) throw new IllegalArgumentException("missing provider");
        Object[] objs = Security.getImpl(algorithm, "MessageDigest", provider);
        if (objs[0] instanceof MessageDigest) {
            MessageDigest md = (MessageDigest)(MessageDigest)objs[0];
            md.provider = (Provider)(Provider)objs[1];
            return md;
        } else {
            MessageDigest delegate = new MessageDigest$Delegate((MessageDigestSpi)(MessageDigestSpi)objs[0], algorithm);
            delegate.provider = (Provider)(Provider)objs[1];
            return delegate;
        }
    }
    
    public static MessageDigest getInstance(String algorithm, Provider provider) throws NoSuchAlgorithmException {
        if (provider == null) throw new IllegalArgumentException("missing provider");
        Object[] objs = Security.getImpl(algorithm, "MessageDigest", provider);
        if (objs[0] instanceof MessageDigest) {
            MessageDigest md = (MessageDigest)(MessageDigest)objs[0];
            md.provider = (Provider)(Provider)objs[1];
            return md;
        } else {
            MessageDigest delegate = new MessageDigest$Delegate((MessageDigestSpi)(MessageDigestSpi)objs[0], algorithm);
            delegate.provider = (Provider)(Provider)objs[1];
            return delegate;
        }
    }
    
    public final Provider getProvider() {
        return this.provider;
    }
    
    public void update(byte input) {
        engineUpdate(input);
        state = IN_PROGRESS;
    }
    
    public void update(byte[] input, int offset, int len) {
        if (input == null) {
            throw new IllegalArgumentException("No input buffer given");
        }
        if (input.length - offset < len) {
            throw new IllegalArgumentException("Input buffer too short");
        }
        engineUpdate(input, offset, len);
        state = IN_PROGRESS;
    }
    
    public void update(byte[] input) {
        engineUpdate(input, 0, input.length);
        state = IN_PROGRESS;
    }
    
    public final void update(ByteBuffer input) {
        if (input == null) {
            throw new NullPointerException();
        }
        engineUpdate(input);
        state = IN_PROGRESS;
    }
    
    public byte[] digest() {
        byte[] result = engineDigest();
        state = INITIAL;
        return result;
    }
    
    public int digest(byte[] buf, int offset, int len) throws DigestException {
        if (buf == null) {
            throw new IllegalArgumentException("No output buffer given");
        }
        if (buf.length - offset < len) {
            throw new IllegalArgumentException("Output buffer too small for specified offset and length");
        }
        int numBytes = engineDigest(buf, offset, len);
        state = INITIAL;
        return numBytes;
    }
    
    public byte[] digest(byte[] input) {
        update(input);
        return digest();
    }
    
    public String toString() {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream p = new PrintStream(baos);
        p.print(algorithm + " Message Digest from " + provider.getName() + ", ");
        switch (state) {
        case INITIAL: 
            p.print("<initialized>");
            break;
        
        case IN_PROGRESS: 
            p.print("<in progress>");
            break;
        
        }
        p.println();
        return (baos.toString());
    }
    
    public static boolean isEqual(byte[] digesta, byte[] digestb) {
        if (digesta.length != digestb.length) return false;
        for (int i = 0; i < digesta.length; i++) {
            if (digesta[i] != digestb[i]) {
                return false;
            }
        }
        return true;
    }
    
    public void reset() {
        engineReset();
        state = INITIAL;
    }
    
    public final String getAlgorithm() {
        return this.algorithm;
    }
    
    public final int getDigestLength() {
        int digestLen = engineGetDigestLength();
        if (digestLen == 0) {
            try {
                MessageDigest md = (MessageDigest)(MessageDigest)clone();
                byte[] digest = md.digest();
                return digest.length;
            } catch (CloneNotSupportedException e) {
                return digestLen;
            }
        }
        return digestLen;
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
}
