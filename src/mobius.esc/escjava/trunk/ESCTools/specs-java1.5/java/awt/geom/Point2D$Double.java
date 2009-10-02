package java.awt.geom;

public class Point2D$Double extends Point2D {
    public double x;
    public double y;
    
    public Point2D$Double() {
        
    }
    
    public Point2D$Double(double x, double y) {
        
        this.x = x;
        this.y = y;
    }
    
    public double getX() {
        return x;
    }
    
    public double getY() {
        return y;
    }
    
    public void setLocation(double x, double y) {
        this.x = x;
        this.y = y;
    }
    
    public String toString() {
        return "Point2D.Double[" + x + ", " + y + "]";
    }
}
