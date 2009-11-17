package javax.sound.sampled;

import java.io.InputStream;
import java.io.IOException;

public class AudioInputStream extends InputStream {
    private InputStream stream;
    protected AudioFormat format;
    protected long frameLength;
    protected int frameSize;
    protected long framePos;
    private long markpos;
    private byte[] pushBackBuffer = null;
    private int pushBackLen = 0;
    private byte[] markPushBackBuffer = null;
    private int markPushBackLen = 0;
    
    public AudioInputStream(InputStream stream, AudioFormat format, long length) {
        
        this.format = format;
        this.frameLength = length;
        this.frameSize = format.getFrameSize();
        if (this.frameSize == AudioSystem.NOT_SPECIFIED || frameSize <= 0) {
            this.frameSize = 1;
        }
        this.stream = stream;
        framePos = 0;
        markpos = 0;
    }
    
    public AudioInputStream(TargetDataLine line) {
        
        AudioInputStream$TargetDataLineInputStream tstream = new AudioInputStream$TargetDataLineInputStream(this, line);
        format = line.getFormat();
        frameLength = AudioSystem.NOT_SPECIFIED;
        frameSize = format.getFrameSize();
        if (frameSize == AudioSystem.NOT_SPECIFIED || frameSize <= 0) {
            frameSize = 1;
        }
        this.stream = tstream;
        framePos = 0;
        markpos = 0;
    }
    
    public AudioFormat getFormat() {
        return format;
    }
    
    public long getFrameLength() {
        return frameLength;
    }
    
    public int read() throws IOException {
        if (frameSize != 1) {
            throw new IOException("cannot read a single byte if frame size > 1");
        }
        byte[] data = new byte[1];
        int temp = read(data);
        if (temp <= 0) {
            return -1;
        }
        return temp & 255;
    }
    
    public int read(byte[] b) throws IOException {
        return read(b, 0, b.length);
    }
    
    public int read(byte[] b, int off, int len) throws IOException {
        if ((len % frameSize) != 0) {
            len -= (len % frameSize);
            if (len == 0) {
                return 0;
            }
        }
        if (frameLength != AudioSystem.NOT_SPECIFIED) {
            if (framePos >= frameLength) {
                return -1;
            } else {
                if ((len / frameSize) > (frameLength - framePos)) {
                    len = (int)(frameLength - framePos) * frameSize;
                }
            }
        }
        int bytesRead = 0;
        int thisOff = off;
        if (pushBackLen > 0 && len >= pushBackLen) {
            System.arraycopy(pushBackBuffer, 0, b, off, pushBackLen);
            thisOff += pushBackLen;
            len -= pushBackLen;
            bytesRead += pushBackLen;
            pushBackLen = 0;
        }
        int thisBytesRead = stream.read(b, thisOff, len);
        if (thisBytesRead == -1) {
            return -1;
        }
        if (thisBytesRead > 0) {
            bytesRead += thisBytesRead;
        }
        if (bytesRead > 0) {
            pushBackLen = bytesRead % frameSize;
            if (pushBackLen > 0) {
                if (pushBackBuffer == null) {
                    pushBackBuffer = new byte[frameSize];
                }
                System.arraycopy(b, off + bytesRead - pushBackLen, pushBackBuffer, 0, pushBackLen);
                bytesRead -= pushBackLen;
            }
            framePos += bytesRead / frameSize;
        }
        return bytesRead;
    }
    
    public long skip(long n) throws IOException {
        if ((n % frameSize) != 0) {
            n -= (n % frameSize);
        }
        if (frameLength != AudioSystem.NOT_SPECIFIED) {
            if ((n / frameSize) > (frameLength - framePos)) {
                n = (frameLength - framePos) * frameSize;
            }
        }
        long temp = stream.skip(n);
        if (temp % frameSize != 0) {
            throw new IOException("Could not skip an integer number of frames.");
        }
        if (temp >= 0) {
            framePos += temp / frameSize;
        }
        return temp;
    }
    
    public int available() throws IOException {
        int temp = stream.available();
        if ((frameLength != AudioSystem.NOT_SPECIFIED) && ((temp / frameSize) > (frameLength - framePos))) {
            return (int)(frameLength - framePos) * frameSize;
        } else {
            return temp;
        }
    }
    
    public void close() throws IOException {
        stream.close();
    }
    
    public void mark(int readlimit) {
        stream.mark(readlimit);
        if (markSupported()) {
            markpos = framePos;
            markPushBackLen = pushBackLen;
            if (markPushBackLen > 0) {
                if (markPushBackBuffer == null) {
                    markPushBackBuffer = new byte[frameSize];
                }
                System.arraycopy(pushBackBuffer, 0, markPushBackBuffer, 0, markPushBackLen);
            }
        }
    }
    
    public void reset() throws IOException {
        stream.reset();
        framePos = markpos;
        pushBackLen = markPushBackLen;
        if (pushBackLen > 0) {
            if (pushBackBuffer == null) {
                pushBackBuffer = new byte[frameSize - 1];
            }
            System.arraycopy(markPushBackBuffer, 0, pushBackBuffer, 0, pushBackLen);
        }
    }
    
    public boolean markSupported() {
        return stream.markSupported();
    }
    {
    }
}
