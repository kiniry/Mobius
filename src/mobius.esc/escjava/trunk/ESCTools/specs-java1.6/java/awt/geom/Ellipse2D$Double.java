package java.awt.geom;

public class Ellipse2D$Double extends Ellipse2D {
    public double x;
    public double y;
    public double width;
    public double height;
    
    public Ellipse2D$Double() {
        
    }
    
    public Ellipse2D$Double(double x, double y, double w, double h) {
        
        setFrame(x, y, w, h);
    }
    
    public double getX() {
        return x;
    }
    
    public double getY() {
        return y;
    }
    
    public double getWidth() {
        return width;
    }
    
    public double getHeight() {
        return height;
    }
    
    public boolean isEmpty() {
        return (width <= 0.0 || height <= 0.0);
    }
    
    public void setFrame(double x, double y, double w, double h) {
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
    }
    
    public Rectangle2D getBounds2D() {
        return new Rectangle2D$Double(x, y, width, height);
    }
}
