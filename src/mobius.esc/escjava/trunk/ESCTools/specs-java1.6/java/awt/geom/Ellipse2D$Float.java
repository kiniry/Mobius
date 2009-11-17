package java.awt.geom;

public class Ellipse2D$Float extends Ellipse2D {
    public float x;
    public float y;
    public float width;
    public float height;
    
    public Ellipse2D$Float() {
        
    }
    
    public Ellipse2D$Float(float x, float y, float w, float h) {
        
        setFrame(x, y, w, h);
    }
    
    public double getX() {
        return (double)x;
    }
    
    public double getY() {
        return (double)y;
    }
    
    public double getWidth() {
        return (double)width;
    }
    
    public double getHeight() {
        return (double)height;
    }
    
    public boolean isEmpty() {
        return (width <= 0.0 || height <= 0.0);
    }
    
    public void setFrame(float x, float y, float w, float h) {
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
    }
    
    public void setFrame(double x, double y, double w, double h) {
        this.x = (float)x;
        this.y = (float)y;
        this.width = (float)w;
        this.height = (float)h;
    }
    
    public Rectangle2D getBounds2D() {
        return new Rectangle2D$Float(x, y, width, height);
    }
}
