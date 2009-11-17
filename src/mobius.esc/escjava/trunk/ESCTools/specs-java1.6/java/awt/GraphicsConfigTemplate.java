package java.awt;

import java.io.*;

public abstract class GraphicsConfigTemplate implements Serializable {
    
    public GraphicsConfigTemplate() {
        
    }
    public static final int REQUIRED = 1;
    public static final int PREFERRED = 2;
    public static final int UNNECESSARY = 3;
    
    public abstract GraphicsConfiguration getBestConfiguration(GraphicsConfiguration[] gc);
    
    public abstract boolean isGraphicsConfigSupported(GraphicsConfiguration gc);
}
