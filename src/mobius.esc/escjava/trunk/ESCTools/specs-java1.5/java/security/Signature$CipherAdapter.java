package java.security;

import java.util.*;
import java.io.*;
import javax.crypto.Cipher;
import javax.crypto.IllegalBlockSizeException;
import javax.crypto.BadPaddingException;
import sun.security.jca.*;

class Signature$CipherAdapter extends SignatureSpi {
    private final Cipher cipher;
    private ByteArrayOutputStream data;
    
    Signature$CipherAdapter(Cipher cipher) {
        
        this.cipher = cipher;
    }
    
    protected void engineInitVerify(PublicKey publicKey) throws InvalidKeyException {
        cipher.init(Cipher.DECRYPT_MODE, publicKey);
        if (data == null) {
            data = new ByteArrayOutputStream(128);
        } else {
            data.reset();
        }
    }
    
    protected void engineInitSign(PrivateKey privateKey) throws InvalidKeyException {
        cipher.init(Cipher.ENCRYPT_MODE, privateKey);
        data = null;
    }
    
    protected void engineInitSign(PrivateKey privateKey, SecureRandom random) throws InvalidKeyException {
        cipher.init(Cipher.ENCRYPT_MODE, privateKey, random);
        data = null;
    }
    
    protected void engineUpdate(byte b) throws SignatureException {
        engineUpdate(new byte[]{b}, 0, 1);
    }
    
    protected void engineUpdate(byte[] b, int off, int len) throws SignatureException {
        if (data != null) {
            data.write(b, off, len);
            return;
        }
        byte[] out = cipher.update(b, off, len);
        if ((out != null) && (out.length != 0)) {
            throw new SignatureException("Cipher unexpectedly returned data");
        }
    }
    
    protected byte[] engineSign() throws SignatureException {
        try {
            return cipher.doFinal();
        } catch (IllegalBlockSizeException e) {
            throw new SignatureException("doFinal() failed", e);
        } catch (BadPaddingException e) {
            throw new SignatureException("doFinal() failed", e);
        }
    }
    
    protected boolean engineVerify(byte[] sigBytes) throws SignatureException {
        try {
            byte[] out = cipher.doFinal(sigBytes);
            byte[] dataBytes = data.toByteArray();
            data.reset();
            return Arrays.equals(out, dataBytes);
        } catch (BadPaddingException e) {
            return false;
        } catch (IllegalBlockSizeException e) {
            throw new SignatureException("doFinal() failed", e);
        }
    }
    
    protected void engineSetParameter(String param, Object value) throws InvalidParameterException {
        throw new InvalidParameterException("Parameters not supported");
    }
    
    protected Object engineGetParameter(String param) throws InvalidParameterException {
        throw new InvalidParameterException("Parameters not supported");
    }
}
