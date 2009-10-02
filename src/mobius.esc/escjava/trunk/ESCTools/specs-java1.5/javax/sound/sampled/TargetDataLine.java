package javax.sound.sampled;

public interface TargetDataLine extends DataLine {
    
    public void open(AudioFormat format, int bufferSize) throws LineUnavailableException;
    
    public void open(AudioFormat format) throws LineUnavailableException;
    
    public int read(byte[] b, int off, int len);
}
