package java.awt.geom;

public class Point2D$Float extends Point2D {
    public float x;
    public float y;
    
    public Point2D$Float() {
        
    }
    
    public Point2D$Float(float x, float y) {
        
        this.x = x;
        this.y = y;
    }
    
    public double getX() {
        return (double)x;
    }
    
    public double getY() {
        return (double)y;
    }
    
    public void setLocation(double x, double y) {
        this.x = (float)x;
        this.y = (float)y;
    }
    
    public void setLocation(float x, float y) {
        this.x = x;
        this.y = y;
    }
    
    public String toString() {
        return "Point2D.Float[" + x + ", " + y + "]";
    }
}
