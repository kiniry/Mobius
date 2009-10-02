package java.security;

import java.io.IOException;
import java.io.InputStream;
import java.io.FilterInputStream;

public class DigestInputStream extends FilterInputStream {
    private boolean on = true;
    protected MessageDigest digest;
    
    public DigestInputStream(InputStream stream, MessageDigest digest) {
        super(stream);
        setMessageDigest(digest);
    }
    
    public MessageDigest getMessageDigest() {
        return digest;
    }
    
    public void setMessageDigest(MessageDigest digest) {
        this.digest = digest;
    }
    
    public int read() throws IOException {
        int ch = in.read();
        if (on && ch != -1) {
            digest.update((byte)ch);
        }
        return ch;
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        int result = in.read(b, off, len);
        if (on && result != -1) {
            digest.update(b, off, result);
        }
        return result;
    }
    
    public void on(boolean on) {
        this.on = on;
    }
    
    public String toString() {
        return "[Digest Input Stream] " + digest.toString();
    }
}
