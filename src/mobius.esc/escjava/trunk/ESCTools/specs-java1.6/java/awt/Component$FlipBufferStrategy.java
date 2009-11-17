package java.awt;

import java.awt.image.BufferStrategy;
import java.awt.image.VolatileImage;
import java.awt.event.*;
import javax.accessibility.*;
import javax.accessibility.*;
import java.util.logging.*;

public class Component$FlipBufferStrategy extends BufferStrategy {
    /*synthetic*/ final Component this$0;
    protected int numBuffers;
    protected BufferCapabilities caps;
    protected Image drawBuffer;
    protected VolatileImage drawVBuffer;
    protected boolean validatedContents;
    
    protected Component$FlipBufferStrategy(/*synthetic*/ final Component this$0, int numBuffers, BufferCapabilities caps) throws AWTException {
        this.this$0 = this$0;
        
        if (!(this$0 instanceof Window) && !(this$0 instanceof Canvas)) {
            throw new ClassCastException("Component must be a Canvas or Window");
        }
        this.numBuffers = numBuffers;
        this.caps = caps;
        createBuffers(numBuffers, caps);
    }
    
    protected void createBuffers(int numBuffers, BufferCapabilities caps) throws AWTException {
        if (numBuffers < 2) {
            throw new IllegalArgumentException("Number of buffers cannot be less than two");
        } else if (this$0.peer == null) {
            throw new IllegalStateException("Component must have a valid peer");
        } else if (caps == null || !caps.isPageFlipping()) {
            throw new IllegalArgumentException("Page flipping capabilities must be specified");
        } else {
            this$0.peer.createBuffers(numBuffers, caps);
        }
    }
    
    protected Image getBackBuffer() {
        if (this$0.peer != null) {
            Image drawBuffer = this$0.peer.getBackBuffer();
            if (drawBuffer instanceof VolatileImage) {
                drawVBuffer = (VolatileImage)(VolatileImage)drawBuffer;
            }
            revalidate();
            return drawBuffer;
        } else {
            throw new IllegalStateException("Component must have a valid peer");
        }
    }
    
    protected void flip(BufferCapabilities$FlipContents flipAction) {
        if (this$0.peer != null) {
            this$0.peer.flip(flipAction);
        } else {
            throw new IllegalStateException("Component must have a valid peer");
        }
    }
    
    protected void destroyBuffers() {
        if (this$0.peer != null) {
            this$0.peer.destroyBuffers();
        } else {
            throw new IllegalStateException("Component must have a valid peer");
        }
    }
    
    public BufferCapabilities getCapabilities() {
        return caps;
    }
    
    public Graphics getDrawGraphics() {
        if (drawBuffer == null) {
            drawBuffer = getBackBuffer();
            if (drawBuffer instanceof VolatileImage) {
                drawVBuffer = (VolatileImage)(VolatileImage)drawBuffer;
            }
        }
        revalidate();
        return drawBuffer.getGraphics();
    }
    
    protected void revalidate() {
        if (drawVBuffer != null) {
            validatedContents = (drawVBuffer.validate(this$0.getGraphicsConfiguration()) == VolatileImage.IMAGE_RESTORED);
        } else {
            validatedContents = false;
        }
    }
    
    public boolean contentsLost() {
        if (drawVBuffer == null) {
            return false;
        }
        return drawVBuffer.contentsLost();
    }
    
    public boolean contentsRestored() {
        return validatedContents;
    }
    
    public void show() {
        flip(caps.getFlipContents());
    }
}
