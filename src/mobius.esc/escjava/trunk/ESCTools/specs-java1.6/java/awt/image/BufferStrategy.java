package java.awt.image;

import java.awt.BufferCapabilities;
import java.awt.Graphics;

public abstract class BufferStrategy {
    
    public BufferStrategy() {
        
    }
    
    public abstract BufferCapabilities getCapabilities();
    
    public abstract Graphics getDrawGraphics();
    
    public abstract boolean contentsLost();
    
    public abstract boolean contentsRestored();
    
    public abstract void show();
}
