package javax.swing.plaf.metal;

import java.awt.*;
import java.awt.image.*;
import java.util.*;

class CachedPainter$Cache$Entry {
    private GraphicsConfiguration config;
    private Object[] args;
    private Image image;
    private int w;
    private int h;
    
    CachedPainter$Cache$Entry(GraphicsConfiguration config, int w, int h, Object[] args) {
        
        this.config = config;
        this.args = args;
        this.w = w;
        this.h = h;
    }
    
    public void setImage(Image image) {
        this.image = image;
    }
    
    public Image getImage() {
        return image;
    }
    
    public String toString() {
        String value = super.toString() + "[ graphicsConfig=" + config + ", image=" + image + ", w=" + w + ", h=" + h;
        if (args != null) {
            for (int counter = 0; counter < args.length; counter++) {
                value += ", " + args[counter];
            }
        }
        value += "]";
        return value;
    }
    
    public boolean equals(GraphicsConfiguration config, int w, int h, Object[] args) {
        if (this.w == w && this.h == h && ((this.config != null && this.config.equals(config)) || (this.config == null && config == null))) {
            if (this.args == null && args == null) {
                return true;
            }
            if (this.args != null && args != null && this.args.length == args.length) {
                for (int counter = args.length - 1; counter >= 0; counter--) {
                    if (!this.args[counter].equals(args[counter])) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
    }
}
