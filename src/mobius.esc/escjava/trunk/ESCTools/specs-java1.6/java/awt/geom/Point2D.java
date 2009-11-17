package java.awt.geom;

public abstract class Point2D implements Cloneable {
    {
    }
    {
    }
    
    protected Point2D() {
        
    }
    
    public abstract double getX();
    
    public abstract double getY();
    
    public abstract void setLocation(double x, double y);
    
    public void setLocation(Point2D p) {
        setLocation(p.getX(), p.getY());
    }
    
    public static double distanceSq(double X1, double Y1, double X2, double Y2) {
        X1 -= X2;
        Y1 -= Y2;
        return (X1 * X1 + Y1 * Y1);
    }
    
    public static double distance(double X1, double Y1, double X2, double Y2) {
        X1 -= X2;
        Y1 -= Y2;
        return Math.sqrt(X1 * X1 + Y1 * Y1);
    }
    
    public double distanceSq(double PX, double PY) {
        PX -= getX();
        PY -= getY();
        return (PX * PX + PY * PY);
    }
    
    public double distanceSq(Point2D pt) {
        double PX = pt.getX() - this.getX();
        double PY = pt.getY() - this.getY();
        return (PX * PX + PY * PY);
    }
    
    public double distance(double PX, double PY) {
        PX -= getX();
        PY -= getY();
        return Math.sqrt(PX * PX + PY * PY);
    }
    
    public double distance(Point2D pt) {
        double PX = pt.getX() - this.getX();
        double PY = pt.getY() - this.getY();
        return Math.sqrt(PX * PX + PY * PY);
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public int hashCode() {
        long bits = java.lang.Double.doubleToLongBits(getX());
        bits ^= java.lang.Double.doubleToLongBits(getY()) * 31;
        return (((int)bits) ^ ((int)(bits >> 32)));
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Point2D) {
            Point2D p2d = (Point2D)(Point2D)obj;
            return (getX() == p2d.getX()) && (getY() == p2d.getY());
        }
        return super.equals(obj);
    }
}
