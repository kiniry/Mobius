package javax.sound.sampled;

import java.io.InputStream;
import java.io.IOException;

class AudioInputStream$TargetDataLineInputStream extends InputStream {
    /*synthetic*/ final AudioInputStream this$0;
    TargetDataLine line;
    
    AudioInputStream$TargetDataLineInputStream(/*synthetic*/ final AudioInputStream this$0, TargetDataLine line) {
        this.this$0 = this$0;
        
        this.line = line;
    }
    
    public int available() throws IOException {
        return line.available();
    }
    
    public void close() throws IOException {
        if (line.isActive()) {
            line.flush();
            line.stop();
        }
        line.close();
    }
    
    public int read() throws IOException {
        byte[] b = new byte[1];
        int value = read(b, 0, 1);
        if (value == -1) {
            return -1;
        }
        value = (int)b[0];
        if (line.getFormat().getEncoding().equals(AudioFormat$Encoding.PCM_SIGNED)) {
            value += 128;
        }
        return value;
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        try {
            return line.read(b, off, len);
        } catch (IllegalArgumentException e) {
            throw new IOException(e.getMessage());
        }
    }
}
