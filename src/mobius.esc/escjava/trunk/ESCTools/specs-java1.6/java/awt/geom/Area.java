package java.awt.geom;

import java.awt.Shape;
import java.awt.Rectangle;
import java.util.Vector;
import java.util.Enumeration;
import sun.awt.geom.Curve;
import sun.awt.geom.Crossings;
import sun.awt.geom.AreaOp;

public class Area implements Shape, Cloneable {
    private static Vector EmptyCurves = new Vector();
    private Vector curves;
    
    public Area() {
        
        curves = EmptyCurves;
    }
    
    public Area(Shape s) {
        
        if (s instanceof Area) {
            curves = ((Area)(Area)s).curves;
            return;
        }
        curves = new Vector();
        PathIterator pi = s.getPathIterator(null);
        int windingRule = pi.getWindingRule();
        double[] coords = new double[23];
        double movx = 0;
        double movy = 0;
        double curx = 0;
        double cury = 0;
        double newx;
        double newy;
        while (!pi.isDone()) {
            switch (pi.currentSegment(coords)) {
            case PathIterator.SEG_MOVETO: 
                Curve.insertLine(curves, curx, cury, movx, movy);
                curx = movx = coords[0];
                cury = movy = coords[1];
                Curve.insertMove(curves, movx, movy);
                break;
            
            case PathIterator.SEG_LINETO: 
                newx = coords[0];
                newy = coords[1];
                Curve.insertLine(curves, curx, cury, newx, newy);
                curx = newx;
                cury = newy;
                break;
            
            case PathIterator.SEG_QUADTO: 
                newx = coords[2];
                newy = coords[3];
                Curve.insertQuad(curves, curx, cury, coords);
                curx = newx;
                cury = newy;
                break;
            
            case PathIterator.SEG_CUBICTO: 
                newx = coords[4];
                newy = coords[5];
                Curve.insertCubic(curves, curx, cury, coords);
                curx = newx;
                cury = newy;
                break;
            
            case PathIterator.SEG_CLOSE: 
                Curve.insertLine(curves, curx, cury, movx, movy);
                curx = movx;
                cury = movy;
                break;
            
            }
            pi.next();
        }
        Curve.insertLine(curves, curx, cury, movx, movy);
        AreaOp operator;
        if (windingRule == PathIterator.WIND_EVEN_ODD) {
            operator = new AreaOp$EOWindOp();
        } else {
            operator = new AreaOp$NZWindOp();
        }
        curves = operator.calculate(this.curves, EmptyCurves);
    }
    
    public void add(Area rhs) {
        curves = new AreaOp$AddOp().calculate(this.curves, rhs.curves);
        invalidateBounds();
    }
    
    public void subtract(Area rhs) {
        curves = new AreaOp$SubOp().calculate(this.curves, rhs.curves);
        invalidateBounds();
    }
    
    public void intersect(Area rhs) {
        curves = new AreaOp$IntOp().calculate(this.curves, rhs.curves);
        invalidateBounds();
    }
    
    public void exclusiveOr(Area rhs) {
        curves = new AreaOp$XorOp().calculate(this.curves, rhs.curves);
        invalidateBounds();
    }
    
    public void reset() {
        curves = new Vector();
        invalidateBounds();
    }
    
    public boolean isEmpty() {
        return (curves.size() == 0);
    }
    
    public boolean isPolygonal() {
        Enumeration enum_ = curves.elements();
        while (enum_.hasMoreElements()) {
            if (((Curve)(Curve)enum_.nextElement()).getOrder() > 1) {
                return false;
            }
        }
        return true;
    }
    
    public boolean isRectangular() {
        int size = curves.size();
        if (size == 0) {
            return true;
        }
        if (size > 3) {
            return false;
        }
        Curve c1 = (Curve)(Curve)curves.get(1);
        Curve c2 = (Curve)(Curve)curves.get(2);
        if (c1.getOrder() != 1 || c2.getOrder() != 1) {
            return false;
        }
        if (c1.getXTop() != c1.getXBot() || c2.getXTop() != c2.getXBot()) {
            return false;
        }
        if (c1.getYTop() != c2.getYTop() || c1.getYBot() != c2.getYBot()) {
            return false;
        }
        return true;
    }
    
    public boolean isSingular() {
        if (curves.size() < 3) {
            return true;
        }
        Enumeration enum_ = curves.elements();
        enum_.nextElement();
        while (enum_.hasMoreElements()) {
            if (((Curve)(Curve)enum_.nextElement()).getOrder() == 0) {
                return false;
            }
        }
        return true;
    }
    private Rectangle2D cachedBounds;
    
    private void invalidateBounds() {
        cachedBounds = null;
    }
    
    private Rectangle2D getCachedBounds() {
        if (cachedBounds != null) {
            return cachedBounds;
        }
        Rectangle2D r = new Rectangle2D$Double();
        if (curves.size() > 0) {
            Curve c = (Curve)(Curve)curves.get(0);
            r.setRect(c.getX0(), c.getY0(), 0, 0);
            for (int i = 1; i < curves.size(); i++) {
                ((Curve)(Curve)curves.get(i)).enlarge(r);
            }
        }
        return (cachedBounds = r);
    }
    
    public Rectangle2D getBounds2D() {
        return getCachedBounds().getBounds2D();
    }
    
    public Rectangle getBounds() {
        return getCachedBounds().getBounds();
    }
    
    public Object clone() {
        return new Area(this);
    }
    
    public boolean equals(Area other) {
        if (other == this) {
            return true;
        }
        if (other == null) {
            return false;
        }
        Vector c = new AreaOp$XorOp().calculate(this.curves, other.curves);
        return c.isEmpty();
    }
    
    public void transform(AffineTransform t) {
        curves = new Area(t.createTransformedShape(this)).curves;
        invalidateBounds();
    }
    
    public Area createTransformedArea(AffineTransform t) {
        return new Area(t.createTransformedShape(this));
    }
    
    public boolean contains(double x, double y) {
        if (!getCachedBounds().contains(x, y)) {
            return false;
        }
        Enumeration enum_ = curves.elements();
        int crossings = 0;
        while (enum_.hasMoreElements()) {
            Curve c = (Curve)(Curve)enum_.nextElement();
            crossings += c.crossingsFor(x, y);
        }
        return ((crossings & 1) == 1);
    }
    
    public boolean contains(Point2D p) {
        return contains(p.getX(), p.getY());
    }
    
    public boolean contains(double x, double y, double w, double h) {
        if (w < 0 || h < 0) {
            return false;
        }
        if (!getCachedBounds().contains(x, y, w, h)) {
            return false;
        }
        Crossings c = Crossings.findCrossings(curves, x, y, x + w, y + h);
        return (c != null && c.covers(y, y + h));
    }
    
    public boolean contains(Rectangle2D p) {
        return contains(p.getX(), p.getY(), p.getWidth(), p.getHeight());
    }
    
    public boolean intersects(double x, double y, double w, double h) {
        if (w < 0 || h < 0) {
            return false;
        }
        if (!getCachedBounds().intersects(x, y, w, h)) {
            return false;
        }
        Crossings c = Crossings.findCrossings(curves, x, y, x + w, y + h);
        return (c == null || !c.isEmpty());
    }
    
    public boolean intersects(Rectangle2D p) {
        return intersects(p.getX(), p.getY(), p.getWidth(), p.getHeight());
    }
    
    public PathIterator getPathIterator(AffineTransform at) {
        return new AreaIterator(curves, at);
    }
    
    public PathIterator getPathIterator(AffineTransform at, double flatness) {
        return new FlatteningPathIterator(getPathIterator(at), flatness);
    }
}
