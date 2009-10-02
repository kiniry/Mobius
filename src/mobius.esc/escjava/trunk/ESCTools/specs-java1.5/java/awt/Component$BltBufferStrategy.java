package java.awt;

import java.awt.image.BufferStrategy;
import java.awt.image.VolatileImage;
import java.awt.event.*;
import javax.accessibility.*;
import javax.accessibility.*;
import java.util.logging.*;

public class Component$BltBufferStrategy extends BufferStrategy {
    /*synthetic*/ final Component this$0;
    protected BufferCapabilities caps;
    protected VolatileImage[] backBuffers;
    protected boolean validatedContents;
    protected int width;
    protected int height;
    
    protected Component$BltBufferStrategy(/*synthetic*/ final Component this$0, int numBuffers, BufferCapabilities caps) {
        this.this$0 = this$0;
        
        this.caps = caps;
        createBackBuffers(numBuffers - 1);
    }
    
    protected void createBackBuffers(int numBuffers) {
        if (numBuffers == 0) {
            backBuffers = null;
        } else {
            width = this$0.getWidth();
            height = this$0.getHeight();
            backBuffers = new VolatileImage[numBuffers];
            for (int i = 0; i < numBuffers; i++) {
                backBuffers[i] = this$0.createVolatileImage(width, height);
            }
        }
    }
    
    public BufferCapabilities getCapabilities() {
        return caps;
    }
    
    public Graphics getDrawGraphics() {
        revalidate();
        Image backBuffer = getBackBuffer();
        if (backBuffer == null) {
            return this$0.getGraphics();
        }
        return backBuffer.getGraphics();
    }
    
    Image getBackBuffer() {
        if (backBuffers != null) {
            return backBuffers[backBuffers.length - 1];
        } else {
            return null;
        }
    }
    
    public void show() {
        if (backBuffers == null) {
            return;
        }
        Graphics g = this$0.getGraphics();
        try {
            for (int i = 0; i < backBuffers.length; i++) {
                g.drawImage(backBuffers[i], 0, 0, this$0);
                g.dispose();
                g = null;
                g = backBuffers[i].getGraphics();
            }
        } finally {
            if (g != null) {
                g.dispose();
            }
        }
    }
    
    protected void revalidate() {
        if (backBuffers == null) {
            validatedContents = false;
        } else if (this$0.getWidth() != width || this$0.getHeight() != height) {
            createBackBuffers(backBuffers.length);
            validatedContents = true;
        } else {
            validatedContents = (backBuffers[backBuffers.length - 1].validate(this$0.getGraphicsConfiguration()) == VolatileImage.IMAGE_RESTORED);
        }
    }
    
    public boolean contentsLost() {
        if (width < this$0.getWidth() || height < this$0.getHeight()) {
            return true;
        } else {
            return backBuffers[backBuffers.length - 1].contentsLost();
        }
    }
    
    public boolean contentsRestored() {
        return validatedContents;
    }
}
