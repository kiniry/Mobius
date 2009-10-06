package javax.sound.sampled;

public interface DataLine extends Line {
    
    public void drain();
    
    public void flush();
    
    public void start();
    
    public void stop();
    
    public boolean isRunning();
    
    public boolean isActive();
    
    public AudioFormat getFormat();
    
    public int getBufferSize();
    
    public int available();
    
    public int getFramePosition();
    
    public long getLongFramePosition();
    
    public long getMicrosecondPosition();
    
    public float getLevel();
}
