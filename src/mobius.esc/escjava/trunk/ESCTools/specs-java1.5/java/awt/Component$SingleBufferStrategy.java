package java.awt;

import java.awt.image.BufferStrategy;
import java.awt.event.*;
import javax.accessibility.*;
import javax.accessibility.*;
import java.util.logging.*;

class Component$SingleBufferStrategy extends BufferStrategy {
    /*synthetic*/ final Component this$0;
    private BufferCapabilities caps;
    
    public Component$SingleBufferStrategy(/*synthetic*/ final Component this$0, BufferCapabilities caps) {
        this.this$0 = this$0;
        
        this.caps = caps;
    }
    
    public BufferCapabilities getCapabilities() {
        return caps;
    }
    
    public Graphics getDrawGraphics() {
        return this$0.getGraphics();
    }
    
    public boolean contentsLost() {
        return false;
    }
    
    public boolean contentsRestored() {
        return false;
    }
    
    public void show() {
    }
}
