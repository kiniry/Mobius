package java.awt.geom;

public class QuadCurve2D$Float extends QuadCurve2D {
    public float x1;
    public float y1;
    public float ctrlx;
    public float ctrly;
    public float x2;
    public float y2;
    
    public QuadCurve2D$Float() {
        
    }
    
    public QuadCurve2D$Float(float x1, float y1, float ctrlx, float ctrly, float x2, float y2) {
        
        setCurve(x1, y1, ctrlx, ctrly, x2, y2);
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
    
    public double getCtrlX() {
        return (double)ctrlx;
    }
    
    public double getCtrlY() {
        return (double)ctrly;
    }
    
    public Point2D getCtrlPt() {
        return new Point2D$Float(ctrlx, ctrly);
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
    
    public void setCurve(double x1, double y1, double ctrlx, double ctrly, double x2, double y2) {
        this.x1 = (float)x1;
        this.y1 = (float)y1;
        this.ctrlx = (float)ctrlx;
        this.ctrly = (float)ctrly;
        this.x2 = (float)x2;
        this.y2 = (float)y2;
    }
    
    public void setCurve(float x1, float y1, float ctrlx, float ctrly, float x2, float y2) {
        this.x1 = x1;
        this.y1 = y1;
        this.ctrlx = ctrlx;
        this.ctrly = ctrly;
        this.x2 = x2;
        this.y2 = y2;
    }
    
    public Rectangle2D getBounds2D() {
        float left = Math.min(Math.min(x1, x2), ctrlx);
        float top = Math.min(Math.min(y1, y2), ctrly);
        float right = Math.max(Math.max(x1, x2), ctrlx);
        float bottom = Math.max(Math.max(y1, y2), ctrly);
        return new Rectangle2D$Float(left, top, right - left, bottom - top);
    }
}
