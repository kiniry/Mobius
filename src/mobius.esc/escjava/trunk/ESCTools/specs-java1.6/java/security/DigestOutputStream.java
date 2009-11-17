package java.security;

import java.io.IOException;
import java.io.OutputStream;
import java.io.FilterOutputStream;

public class DigestOutputStream extends FilterOutputStream {
    private boolean on = true;
    protected MessageDigest digest;
    
    public DigestOutputStream(OutputStream stream, MessageDigest digest) {
        super(stream);
        setMessageDigest(digest);
    }
    
    public MessageDigest getMessageDigest() {
        return digest;
    }
    
    public void setMessageDigest(MessageDigest digest) {
        this.digest = digest;
    }
    
    public void write(int b) throws IOException {
        if (on) {
            digest.update((byte)b);
        }
        out.write(b);
    }
    
    public void write(byte[] b, int off, int len) throws IOException {
        if (on) {
            digest.update(b, off, len);
        }
        out.write(b, off, len);
    }
    
    public void on(boolean on) {
        this.on = on;
    }
    
    public String toString() {
        return "[Digest Output Stream] " + digest.toString();
    }
}
