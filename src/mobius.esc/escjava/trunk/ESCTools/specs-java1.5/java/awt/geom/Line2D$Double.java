package java.awt.geom;

public class Line2D$Double extends Line2D {
    public double x1;
    public double y1;
    public double x2;
    public double y2;
    
    public Line2D$Double() {
        
    }
    
    public Line2D$Double(double X1, double Y1, double X2, double Y2) {
        
        setLine(X1, Y1, X2, Y2);
    }
    
    public Line2D$Double(Point2D p1, Point2D p2) {
        
        setLine(p1, p2);
    }
    
    public double getX1() {
        return x1;
    }
    
    public double getY1() {
        return y1;
    }
    
    public Point2D getP1() {
        return new Point2D$Double(x1, y1);
    }
    
    public double getX2() {
        return x2;
    }
    
    public double getY2() {
        return y2;
    }
    
    public Point2D getP2() {
        return new Point2D$Double(x2, y2);
    }
    
    public void setLine(double X1, double Y1, double X2, double Y2) {
        this.x1 = X1;
        this.y1 = Y1;
        this.x2 = X2;
        this.y2 = Y2;
    }
    
    public Rectangle2D getBounds2D() {
        double x;
        double y;
        double w;
        double h;
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
        return new Rectangle2D$Double(x, y, w, h);
    }
}
