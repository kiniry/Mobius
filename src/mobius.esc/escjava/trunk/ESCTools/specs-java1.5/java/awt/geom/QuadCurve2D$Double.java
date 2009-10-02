package java.awt.geom;

public class QuadCurve2D$Double extends QuadCurve2D {
    public double x1;
    public double y1;
    public double ctrlx;
    public double ctrly;
    public double x2;
    public double y2;
    
    public QuadCurve2D$Double() {
        
    }
    
    public QuadCurve2D$Double(double x1, double y1, double ctrlx, double ctrly, double x2, double y2) {
        
        setCurve(x1, y1, ctrlx, ctrly, x2, y2);
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
    
    public double getCtrlX() {
        return ctrlx;
    }
    
    public double getCtrlY() {
        return ctrly;
    }
    
    public Point2D getCtrlPt() {
        return new Point2D$Double(ctrlx, ctrly);
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
    
    public void setCurve(double x1, double y1, double ctrlx, double ctrly, double x2, double y2) {
        this.x1 = x1;
        this.y1 = y1;
        this.ctrlx = ctrlx;
        this.ctrly = ctrly;
        this.x2 = x2;
        this.y2 = y2;
    }
    
    public Rectangle2D getBounds2D() {
        double left = Math.min(Math.min(x1, x2), ctrlx);
        double top = Math.min(Math.min(y1, y2), ctrly);
        double right = Math.max(Math.max(x1, x2), ctrlx);
        double bottom = Math.max(Math.max(y1, y2), ctrly);
        return new Rectangle2D$Double(left, top, right - left, bottom - top);
    }
}
