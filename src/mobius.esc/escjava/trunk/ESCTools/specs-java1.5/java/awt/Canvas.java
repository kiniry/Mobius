package java.awt;

import java.awt.image.BufferStrategy;
import javax.accessibility.*;

public class Canvas extends Component implements Accessible {
    private static final String base = "canvas";
    private static int nameCounter = 0;
    private static final long serialVersionUID = -2284879212465893870L;
    
    public Canvas() {
        
    }
    
    public Canvas(GraphicsConfiguration config) {
        this();
        graphicsConfig = config;
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) peer = getToolkit().createCanvas(this);
            super.addNotify();
        }
    }
    
    public void paint(Graphics g) {
        g.clearRect(0, 0, width, height);
    }
    
    public void update(Graphics g) {
        g.clearRect(0, 0, width, height);
        paint(g);
    }
    
    boolean postsOldMouseEvents() {
        return true;
    }
    
    public void createBufferStrategy(int numBuffers) {
        super.createBufferStrategy(numBuffers);
    }
    
    public void createBufferStrategy(int numBuffers, BufferCapabilities caps) throws AWTException {
        super.createBufferStrategy(numBuffers, caps);
    }
    
    public BufferStrategy getBufferStrategy() {
        return super.getBufferStrategy();
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Canvas$AccessibleAWTCanvas(this);
        }
        return accessibleContext;
    }
    {
    }
}
