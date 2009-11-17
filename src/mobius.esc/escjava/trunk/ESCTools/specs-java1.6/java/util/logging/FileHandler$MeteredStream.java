package java.util.logging;

import java.io.*;
import java.security.*;

class FileHandler$MeteredStream extends OutputStream {
    /*synthetic*/ final FileHandler this$0;
    OutputStream out;
    int written;
    
    FileHandler$MeteredStream(/*synthetic*/ final FileHandler this$0, OutputStream out, int written) {
        this.this$0 = this$0;
        
        this.out = out;
        this.written = written;
    }
    
    public void write(int b) throws IOException {
        out.write(b);
        written++;
    }
    
    public void write(byte[] buff) throws IOException {
        out.write(buff);
        written += buff.length;
    }
    
    public void write(byte[] buff, int off, int len) throws IOException {
        out.write(buff, off, len);
        written += len;
    }
    
    public void flush() throws IOException {
        out.flush();
    }
    
    public void close() throws IOException {
        out.close();
    }
}
