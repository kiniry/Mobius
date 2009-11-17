package javax.sound.sampled;

public interface Line {
    
    public Line$Info getLineInfo();
    
    public void open() throws LineUnavailableException;
    
    public void close();
    
    public boolean isOpen();
    
    public Control[] getControls();
    
    public boolean isControlSupported(Control$Type control);
    
    public Control getControl(Control$Type control);
    
    public void addLineListener(LineListener listener);
    
    public void removeLineListener(LineListener listener);
}
