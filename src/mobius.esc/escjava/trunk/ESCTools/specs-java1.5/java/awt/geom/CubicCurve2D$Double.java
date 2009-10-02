package java.awt.geom;

public class CubicCurve2D$Double extends CubicCurve2D {
    public double x1;
    public double y1;
    public double ctrlx1;
    public double ctrly1;
    public double ctrlx2;
    public double ctrly2;
    public double x2;
    public double y2;
    
    public CubicCurve2D$Double() {
        
    }
    
    public CubicCurve2D$Double(double x1, double y1, double ctrlx1, double ctrly1, double ctrlx2, double ctrly2, double x2, double y2) {
        
        setCurve(x1, y1, ctrlx1, ctrly1, ctrlx2, ctrly2, x2, y2);
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
    
    public double getCtrlX1() {
        return ctrlx1;
    }
    
    public double getCtrlY1() {
        return ctrly1;
    }
    
    public Point2D getCtrlP1() {
        return new Point2D$Double(ctrlx1, ctrly1);
    }
    
    public double getCtrlX2() {
        return ctrlx2;
    }
    
    public double getCtrlY2() {
        return ctrly2;
    }
    
    public Point2D getCtrlP2() {
        return new Point2D$Double(ctrlx2, ctrly2);
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
    
    public void setCurve(double x1, double y1, double ctrlx1, double ctrly1, double ctrlx2, double ctrly2, double x2, double y2) {
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
        double left = Math.min(Math.min(x1, x2), Math.min(ctrlx1, ctrlx2));
        double top = Math.min(Math.min(y1, y2), Math.min(ctrly1, ctrly2));
        double right = Math.max(Math.max(x1, x2), Math.max(ctrlx1, ctrlx2));
        double bottom = Math.max(Math.max(y1, y2), Math.max(ctrly1, ctrly2));
        return new Rectangle2D$Double(left, top, right - left, bottom - top);
    }
}
