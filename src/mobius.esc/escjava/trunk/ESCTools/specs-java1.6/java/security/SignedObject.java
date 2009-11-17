package java.security;

import java.io.*;

public final class SignedObject implements Serializable {
    private static final long serialVersionUID = 720502720485447167L;
    private byte[] content;
    private byte[] signature;
    private String thealgorithm;
    
    public SignedObject(Serializable object, PrivateKey signingKey, Signature signingEngine) throws IOException, InvalidKeyException, SignatureException {
        
        ByteArrayOutputStream b = new ByteArrayOutputStream();
        ObjectOutput a = new ObjectOutputStream(b);
        a.writeObject(object);
        a.flush();
        a.close();
        this.content = b.toByteArray();
        b.close();
        this.sign(signingKey, signingEngine);
    }
    
    public Object getObject() throws IOException, ClassNotFoundException {
        ByteArrayInputStream b = new ByteArrayInputStream(this.content);
        ObjectInput a = new ObjectInputStream(b);
        Object obj = a.readObject();
        b.close();
        a.close();
        return obj;
    }
    
    public byte[] getSignature() {
        byte[] sig = (byte[])(byte[])this.signature.clone();
        return sig;
    }
    
    public String getAlgorithm() {
        return this.thealgorithm;
    }
    
    public boolean verify(PublicKey verificationKey, Signature verificationEngine) throws InvalidKeyException, SignatureException {
        verificationEngine.initVerify(verificationKey);
        verificationEngine.update((byte[])(byte[])this.content.clone());
        return verificationEngine.verify((byte[])(byte[])this.signature.clone());
    }
    
    private void sign(PrivateKey signingKey, Signature signingEngine) throws InvalidKeyException, SignatureException {
        signingEngine.initSign(signingKey);
        signingEngine.update((byte[])(byte[])this.content.clone());
        this.signature = (byte[])(byte[])signingEngine.sign().clone();
        this.thealgorithm = signingEngine.getAlgorithm();
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        content = (byte[])(byte[])content.clone();
        signature = (byte[])(byte[])signature.clone();
    }
}
