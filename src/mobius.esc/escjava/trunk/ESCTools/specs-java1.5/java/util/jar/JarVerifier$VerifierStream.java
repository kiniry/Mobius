package java.util.jar;

import java.io.*;
import java.util.*;
import java.util.zip.*;
import java.security.*;
import sun.security.util.ManifestEntryVerifier;

class JarVerifier$VerifierStream extends java.io.InputStream {
    private InputStream is;
    private JarVerifier jv;
    private ManifestEntryVerifier mev;
    private long numLeft;
    
    JarVerifier$VerifierStream(Manifest man, JarEntry je, InputStream is, JarVerifier jv) throws IOException {
        
        this.is = is;
        this.jv = jv;
        this.mev = new ManifestEntryVerifier(man);
        this.jv.beginEntry(je, mev);
        this.numLeft = je.getSize();
        if (this.numLeft == 0) this.jv.update(-1, this.mev);
    }
    
    public int read() throws IOException {
        if (numLeft > 0) {
            int b = is.read();
            jv.update(b, mev);
            numLeft--;
            if (numLeft == 0) jv.update(-1, mev);
            return b;
        } else {
            return -1;
        }
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        if ((numLeft > 0) && (numLeft < len)) {
            len = (int)numLeft;
        }
        if (numLeft > 0) {
            int n = is.read(b, off, len);
            jv.update(n, b, off, len, mev);
            numLeft -= n;
            if (numLeft == 0) jv.update(-1, b, off, len, mev);
            return n;
        } else {
            return -1;
        }
    }
    
    public void close() throws IOException {
        if (is != null) is.close();
        is = null;
        mev = null;
        jv = null;
    }
    
    public int available() throws IOException {
        return is.available();
    }
}
