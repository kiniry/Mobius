package java.security;

import java.security.spec.AlgorithmParameterSpec;
import java.util.*;
import java.io.*;
import java.nio.ByteBuffer;
import sun.security.jca.JCAUtil;

public abstract class SignatureSpi {
    
    public SignatureSpi() {
        
    }
    protected SecureRandom appRandom = null;
    
    protected abstract void engineInitVerify(PublicKey publicKey) throws InvalidKeyException;
    
    protected abstract void engineInitSign(PrivateKey privateKey) throws InvalidKeyException;
    
    protected void engineInitSign(PrivateKey privateKey, SecureRandom random) throws InvalidKeyException {
        this.appRandom = random;
        engineInitSign(privateKey);
    }
    
    protected abstract void engineUpdate(byte b) throws SignatureException;
    
    protected abstract void engineUpdate(byte[] b, int off, int len) throws SignatureException;
    
    protected void engineUpdate(ByteBuffer input) {
        if (input.hasRemaining() == false) {
            return;
        }
        try {
            if (input.hasArray()) {
                byte[] b = input.array();
                int ofs = input.arrayOffset();
                int pos = input.position();
                int lim = input.limit();
                engineUpdate(b, ofs + pos, lim - pos);
                input.position(lim);
            } else {
                int len = input.remaining();
                byte[] b = new byte[JCAUtil.getTempArraySize(len)];
                while (len > 0) {
                    int chunk = Math.min(len, b.length);
                    input.get(b, 0, chunk);
                    engineUpdate(b, 0, chunk);
                    len -= chunk;
                }
            }
        } catch (SignatureException e) {
            throw new ProviderException("update() failed", e);
        }
    }
    
    protected abstract byte[] engineSign() throws SignatureException;
    
    protected int engineSign(byte[] outbuf, int offset, int len) throws SignatureException {
        byte[] sig = engineSign();
        if (len < sig.length) {
            throw new SignatureException("partial signatures not returned");
        }
        if (outbuf.length - offset < sig.length) {
            throw new SignatureException("insufficient space in the output buffer to store the signature");
        }
        System.arraycopy(sig, 0, outbuf, offset, sig.length);
        return sig.length;
    }
    
    protected abstract boolean engineVerify(byte[] sigBytes) throws SignatureException;
    
    protected boolean engineVerify(byte[] sigBytes, int offset, int length) throws SignatureException {
        byte[] sigBytesCopy = new byte[length];
        System.arraycopy(sigBytes, offset, sigBytesCopy, 0, length);
        return engineVerify(sigBytesCopy);
    }
    
    
    protected abstract void engineSetParameter(String param, Object value) throws InvalidParameterException;
    
    protected void engineSetParameter(AlgorithmParameterSpec params) throws InvalidAlgorithmParameterException {
        throw new UnsupportedOperationException();
    }
    
    protected AlgorithmParameters engineGetParameters() {
        throw new UnsupportedOperationException();
    }
    
    
    protected abstract Object engineGetParameter(String param) throws InvalidParameterException;
    
    public Object clone() throws CloneNotSupportedException {
        if (this instanceof Cloneable) {
            return super.clone();
        } else {
            throw new CloneNotSupportedException();
        }
    }
}
