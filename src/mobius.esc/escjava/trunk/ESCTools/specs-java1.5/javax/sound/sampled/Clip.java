package javax.sound.sampled;

import java.io.IOException;

public interface Clip extends DataLine {
    public static final int LOOP_CONTINUOUSLY = -1;
    
    public void open(AudioFormat format, byte[] data, int offset, int bufferSize) throws LineUnavailableException;
    
    public void open(AudioInputStream stream) throws LineUnavailableException, IOException;
    
    public int getFrameLength();
    
    public long getMicrosecondLength();
    
    public void setFramePosition(int frames);
    
    public void setMicrosecondPosition(long microseconds);
    
    public void setLoopPoints(int start, int end);
    
    public void loop(int count);
}
