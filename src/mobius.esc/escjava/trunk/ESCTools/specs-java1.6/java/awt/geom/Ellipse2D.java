package java.awt.geom;

public abstract class Ellipse2D extends RectangularShape {
    {
    }
    {
    }
    
    protected Ellipse2D() {
        
    }
    
    public boolean contains(double x, double y) {
        double ellw = getWidth();
        if (ellw <= 0.0) {
            return false;
        }
        double normx = (x - getX()) / ellw - 0.5;
        double ellh = getHeight();
        if (ellh <= 0.0) {
            return false;
        }
        double normy = (y - getY()) / ellh - 0.5;
        return (normx * normx + normy * normy) < 0.25;
    }
    
    public boolean intersects(double x, double y, double w, double h) {
        if (w <= 0.0 || h <= 0.0) {
            return false;
        }
        double ellw = getWidth();
        if (ellw <= 0.0) {
            return false;
        }
        double normx0 = (x - getX()) / ellw - 0.5;
        double normx1 = normx0 + w / ellw;
        double ellh = getHeight();
        if (ellh <= 0.0) {
            return false;
        }
        double normy0 = (y - getY()) / ellh - 0.5;
        double normy1 = normy0 + h / ellh;
        double nearx;
        double neary;
        if (normx0 > 0.0) {
            nearx = normx0;
        } else if (normx1 < 0.0) {
            nearx = normx1;
        } else {
            nearx = 0.0;
        }
        if (normy0 > 0.0) {
            neary = normy0;
        } else if (normy1 < 0.0) {
            neary = normy1;
        } else {
            neary = 0.0;
        }
        return (nearx * nearx + neary * neary) < 0.25;
    }
    
    public boolean contains(double x, double y, double w, double h) {
        return (contains(x, y) && contains(x + w, y) && contains(x, y + h) && contains(x + w, y + h));
    }
    
    public PathIterator getPathIterator(AffineTransform at) {
        return new EllipseIterator(this, at);
    }
}
