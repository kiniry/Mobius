package java.awt;

public class BufferCapabilities implements Cloneable {
    private ImageCapabilities frontCaps;
    private ImageCapabilities backCaps;
    private BufferCapabilities$FlipContents flipContents;
    
    public BufferCapabilities(ImageCapabilities frontCaps, ImageCapabilities backCaps, BufferCapabilities$FlipContents flipContents) {
        
        if (frontCaps == null || backCaps == null) {
            throw new IllegalArgumentException("Image capabilities specified cannot be null");
        }
        this.frontCaps = frontCaps;
        this.backCaps = backCaps;
        this.flipContents = flipContents;
    }
    
    public ImageCapabilities getFrontBufferCapabilities() {
        return frontCaps;
    }
    
    public ImageCapabilities getBackBufferCapabilities() {
        return backCaps;
    }
    
    public boolean isPageFlipping() {
        return (getFlipContents() != null);
    }
    
    public BufferCapabilities$FlipContents getFlipContents() {
        return flipContents;
    }
    
    public boolean isFullScreenRequired() {
        return false;
    }
    
    public boolean isMultiBufferAvailable() {
        return false;
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    {
    }
}
