package javax.sound.sampled;

public interface Mixer extends Line {
    
    public Mixer$Info getMixerInfo();
    
    public Line$Info[] getSourceLineInfo();
    
    public Line$Info[] getTargetLineInfo();
    
    public Line$Info[] getSourceLineInfo(Line$Info info);
    
    public Line$Info[] getTargetLineInfo(Line$Info info);
    
    public boolean isLineSupported(Line$Info info);
    
    public Line getLine(Line$Info info) throws LineUnavailableException;
    
    public int getMaxLines(Line$Info info);
    
    public Line[] getSourceLines();
    
    public Line[] getTargetLines();
    
    public void synchronize(Line[] lines, boolean maintainSync);
    
    public void unsynchronize(Line[] lines);
    
    public boolean isSynchronizationSupported(Line[] lines, boolean maintainSync);
    {
    }
}
