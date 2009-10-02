package java.security;

import java.util.*;
import java.lang.*;
import java.nio.ByteBuffer;

class MessageDigest$Delegate extends MessageDigest {
    private MessageDigestSpi digestSpi;
    
    public MessageDigest$Delegate(MessageDigestSpi digestSpi, String algorithm) {
        super(algorithm);
        this.digestSpi = digestSpi;
    }
    
    public Object clone() throws CloneNotSupportedException {
        if (digestSpi instanceof Cloneable) {
            MessageDigestSpi digestSpiClone = (MessageDigestSpi)(MessageDigestSpi)digestSpi.clone();
            MessageDigest that = new MessageDigest$Delegate(digestSpiClone, MessageDigest.access$000(((MessageDigest)this)));
            MessageDigest.access$102(that, MessageDigest.access$100(((MessageDigest)this)));
            MessageDigest.access$202(that, MessageDigest.access$200(((MessageDigest)this)));
            return that;
        } else {
            throw new CloneNotSupportedException();
        }
    }
    
    protected int engineGetDigestLength() {
        return digestSpi.engineGetDigestLength();
    }
    
    protected void engineUpdate(byte input) {
        digestSpi.engineUpdate(input);
    }
    
    protected void engineUpdate(byte[] input, int offset, int len) {
        digestSpi.engineUpdate(input, offset, len);
    }
    
    protected void engineUpdate(ByteBuffer input) {
        digestSpi.engineUpdate(input);
    }
    
    protected byte[] engineDigest() {
        return digestSpi.engineDigest();
    }
    
    protected int engineDigest(byte[] buf, int offset, int len) throws DigestException {
        return digestSpi.engineDigest(buf, offset, len);
    }
    
    protected void engineReset() {
        digestSpi.engineReset();
    }
}
