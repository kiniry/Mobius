package java.awt.geom;

public class Line2D$Float extends Line2D {
    public float x1;
    public float y1;
    public float x2;
    public float y2;
    
    public Line2D$Float() {
        
    }
    
    public Line2D$Float(float X1, float Y1, float X2, float Y2) {
        
        setLine(X1, Y1, X2, Y2);
    }
    
    public Line2D$Float(Point2D p1, Point2D p2) {
        
        setLine(p1, p2);
    }
    
    public double getX1() {
        return (double)x1;
    }
    
    public double getY1() {
        return (double)y1;
    }
    
    public Point2D getP1() {
        return new Point2D$Float(x1, y1);
    }
    
    public double getX2() {
        return (double)x2;
    }
    
    public double getY2() {
        return (double)y2;
    }
    
    public Point2D getP2() {
        return new Point2D$Float(x2, y2);
    }
    
    public void setLine(double X1, double Y1, double X2, double Y2) {
        this.x1 = (float)X1;
        this.y1 = (float)Y1;
        this.x2 = (float)X2;
        this.y2 = (float)Y2;
    }
    
    public void setLine(float X1, float Y1, float X2, float Y2) {
        this.x1 = X1;
        this.y1 = Y1;
        this.x2 = X2;
        this.y2 = Y2;
    }
    
    public Rectangle2D getBounds2D() {
        float x;
        float y;
        float w;
        float h;
        if (x1 < x2) {
            x = x1;
            w = x2 - x1;
        } else {
            x = x2;
            w = x1 - x2;
        }
        if (y1 < y2) {
            y = y1;
            h = y2 - y1;
        } else {
            y = y2;
            h = y1 - y2;
        }
        return new Rectangle2D$Float(x, y, w, h);
    }
}
