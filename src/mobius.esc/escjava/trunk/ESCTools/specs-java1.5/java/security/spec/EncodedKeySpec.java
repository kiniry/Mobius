package java.security.spec;

public abstract class EncodedKeySpec implements KeySpec {
    private byte[] encodedKey;
    
    public EncodedKeySpec(byte[] encodedKey) {
        
        this.encodedKey = (byte[])(byte[])encodedKey.clone();
    }
    
    public byte[] getEncoded() {
        return (byte[])(byte[])this.encodedKey.clone();
    }
    
    public abstract String getFormat();
}
