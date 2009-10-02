package java.awt.geom;

import java.awt.Shape;
import java.awt.Rectangle;

public abstract class Line2D implements Shape, Cloneable {
    {
    }
    {
    }
    
    protected Line2D() {
        
    }
    
    public abstract double getX1();
    
    public abstract double getY1();
    
    public abstract Point2D getP1();
    
    public abstract double getX2();
    
    public abstract double getY2();
    
    public abstract Point2D getP2();
    
    public abstract void setLine(double X1, double Y1, double X2, double Y2);
    
    public void setLine(Point2D p1, Point2D p2) {
        setLine(p1.getX(), p1.getY(), p2.getX(), p2.getY());
    }
    
    public void setLine(Line2D l) {
        setLine(l.getX1(), l.getY1(), l.getX2(), l.getY2());
    }
    
    public static int relativeCCW(double X1, double Y1, double X2, double Y2, double PX, double PY) {
        X2 -= X1;
        Y2 -= Y1;
        PX -= X1;
        PY -= Y1;
        double ccw = PX * Y2 - PY * X2;
        if (ccw == 0.0) {
            ccw = PX * X2 + PY * Y2;
            if (ccw > 0.0) {
                PX -= X2;
                PY -= Y2;
                ccw = PX * X2 + PY * Y2;
                if (ccw < 0.0) {
                    ccw = 0.0;
                }
            }
        }
        return (ccw < 0.0) ? -1 : ((ccw > 0.0) ? 1 : 0);
    }
    
    public int relativeCCW(double PX, double PY) {
        return relativeCCW(getX1(), getY1(), getX2(), getY2(), PX, PY);
    }
    
    public int relativeCCW(Point2D p) {
        return relativeCCW(getX1(), getY1(), getX2(), getY2(), p.getX(), p.getY());
    }
    
    public static boolean linesIntersect(double X1, double Y1, double X2, double Y2, double X3, double Y3, double X4, double Y4) {
        return ((relativeCCW(X1, Y1, X2, Y2, X3, Y3) * relativeCCW(X1, Y1, X2, Y2, X4, Y4) <= 0) && (relativeCCW(X3, Y3, X4, Y4, X1, Y1) * relativeCCW(X3, Y3, X4, Y4, X2, Y2) <= 0));
    }
    
    public boolean intersectsLine(double X1, double Y1, double X2, double Y2) {
        return linesIntersect(X1, Y1, X2, Y2, getX1(), getY1(), getX2(), getY2());
    }
    
    public boolean intersectsLine(Line2D l) {
        return linesIntersect(l.getX1(), l.getY1(), l.getX2(), l.getY2(), getX1(), getY1(), getX2(), getY2());
    }
    
    public static double ptSegDistSq(double X1, double Y1, double X2, double Y2, double PX, double PY) {
        X2 -= X1;
        Y2 -= Y1;
        PX -= X1;
        PY -= Y1;
        double dotprod = PX * X2 + PY * Y2;
        double projlenSq;
        if (dotprod <= 0.0) {
            projlenSq = 0.0;
        } else {
            PX = X2 - PX;
            PY = Y2 - PY;
            dotprod = PX * X2 + PY * Y2;
            if (dotprod <= 0.0) {
                projlenSq = 0.0;
            } else {
                projlenSq = dotprod * dotprod / (X2 * X2 + Y2 * Y2);
            }
        }
        double lenSq = PX * PX + PY * PY - projlenSq;
        if (lenSq < 0) {
            lenSq = 0;
        }
        return lenSq;
    }
    
    public static double ptSegDist(double X1, double Y1, double X2, double Y2, double PX, double PY) {
        return Math.sqrt(ptSegDistSq(X1, Y1, X2, Y2, PX, PY));
    }
    
    public double ptSegDistSq(double PX, double PY) {
        return ptSegDistSq(getX1(), getY1(), getX2(), getY2(), PX, PY);
    }
    
    public double ptSegDistSq(Point2D pt) {
        return ptSegDistSq(getX1(), getY1(), getX2(), getY2(), pt.getX(), pt.getY());
    }
    
    public double ptSegDist(double PX, double PY) {
        return ptSegDist(getX1(), getY1(), getX2(), getY2(), PX, PY);
    }
    
    public double ptSegDist(Point2D pt) {
        return ptSegDist(getX1(), getY1(), getX2(), getY2(), pt.getX(), pt.getY());
    }
    
    public static double ptLineDistSq(double X1, double Y1, double X2, double Y2, double PX, double PY) {
        X2 -= X1;
        Y2 -= Y1;
        PX -= X1;
        PY -= Y1;
        double dotprod = PX * X2 + PY * Y2;
        double projlenSq = dotprod * dotprod / (X2 * X2 + Y2 * Y2);
        double lenSq = PX * PX + PY * PY - projlenSq;
        if (lenSq < 0) {
            lenSq = 0;
        }
        return lenSq;
    }
    
    public static double ptLineDist(double X1, double Y1, double X2, double Y2, double PX, double PY) {
        return Math.sqrt(ptLineDistSq(X1, Y1, X2, Y2, PX, PY));
    }
    
    public double ptLineDistSq(double PX, double PY) {
        return ptLineDistSq(getX1(), getY1(), getX2(), getY2(), PX, PY);
    }
    
    public double ptLineDistSq(Point2D pt) {
        return ptLineDistSq(getX1(), getY1(), getX2(), getY2(), pt.getX(), pt.getY());
    }
    
    public double ptLineDist(double PX, double PY) {
        return ptLineDist(getX1(), getY1(), getX2(), getY2(), PX, PY);
    }
    
    public double ptLineDist(Point2D pt) {
        return ptLineDist(getX1(), getY1(), getX2(), getY2(), pt.getX(), pt.getY());
    }
    
    public boolean contains(double x, double y) {
        return false;
    }
    
    public boolean contains(Point2D p) {
        return false;
    }
    
    public boolean intersects(double x, double y, double w, double h) {
        return intersects(new Rectangle2D$Double(x, y, w, h));
    }
    
    public boolean intersects(Rectangle2D r) {
        return r.intersectsLine(getX1(), getY1(), getX2(), getY2());
    }
    
    public boolean contains(double x, double y, double w, double h) {
        return false;
    }
    
    public boolean contains(Rectangle2D r) {
        return false;
    }
    
    public Rectangle getBounds() {
        return getBounds2D().getBounds();
    }
    
    public PathIterator getPathIterator(AffineTransform at) {
        return new LineIterator(this, at);
    }
    
    public PathIterator getPathIterator(AffineTransform at, double flatness) {
        return new LineIterator(this, at);
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
}
