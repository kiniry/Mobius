package java.awt.geom;

public class CubicCurve2D$Float extends CubicCurve2D {
    public float x1;
    public float y1;
    public float ctrlx1;
    public float ctrly1;
    public float ctrlx2;
    public float ctrly2;
    public float x2;
    public float y2;
    
    public CubicCurve2D$Float() {
        
    }
    
    public CubicCurve2D$Float(float x1, float y1, float ctrlx1, float ctrly1, float ctrlx2, float ctrly2, float x2, float y2) {
        
        setCurve(x1, y1, ctrlx1, ctrly1, ctrlx2, ctrly2, x2, y2);
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
    
    public double getCtrlX1() {
        return (double)ctrlx1;
    }
    
    public double getCtrlY1() {
        return (double)ctrly1;
    }
    
    public Point2D getCtrlP1() {
        return new Point2D$Float(ctrlx1, ctrly1);
    }
    
    public double getCtrlX2() {
        return (double)ctrlx2;
    }
    
    public double getCtrlY2() {
        return (double)ctrly2;
    }
    
    public Point2D getCtrlP2() {
        return new Point2D$Float(ctrlx2, ctrly2);
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
    
    public void setCurve(double x1, double y1, double ctrlx1, double ctrly1, double ctrlx2, double ctrly2, double x2, double y2) {
        this.x1 = (float)x1;
        this.y1 = (float)y1;
        this.ctrlx1 = (float)ctrlx1;
        this.ctrly1 = (float)ctrly1;
        this.ctrlx2 = (float)ctrlx2;
        this.ctrly2 = (float)ctrly2;
        this.x2 = (float)x2;
        this.y2 = (float)y2;
    }
    
    public void setCurve(float x1, float y1, float ctrlx1, float ctrly1, float ctrlx2, float ctrly2, float x2, float y2) {
        this.x1 = x1;
        this.y1 = y1;
        this.ctrlx1 = ctrlx1;
        this.ctrly1 = ctrly1;
        this.ctrlx2 = ctrlx2;
        this.ctrly2 = ctrly2;
        this.x2 = x2;
        this.y2 = y2;
    }
    
    public Rectangle2D getBounds2D() {
        float left = Math.min(Math.min(x1, x2), Math.min(ctrlx1, ctrlx2));
        float top = Math.min(Math.min(y1, y2), Math.min(ctrly1, ctrly2));
        float right = Math.max(Math.max(x1, x2), Math.max(ctrlx1, ctrlx2));
        float bottom = Math.max(Math.max(y1, y2), Math.max(ctrly1, ctrly2));
        return new Rectangle2D$Float(left, top, right - left, bottom - top);
    }
}
