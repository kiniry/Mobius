package java.awt.geom;

public abstract class RoundRectangle2D extends RectangularShape {
    {
    }
    {
    }
    
    protected RoundRectangle2D() {
        
    }
    
    public abstract double getArcWidth();
    
    public abstract double getArcHeight();
    
    public abstract void setRoundRect(double x, double y, double w, double h, double arcWidth, double arcHeight);
    
    public void setRoundRect(RoundRectangle2D rr) {
        setRoundRect(rr.getX(), rr.getY(), rr.getWidth(), rr.getHeight(), rr.getArcWidth(), rr.getArcHeight());
    }
    
    public void setFrame(double x, double y, double w, double h) {
        setRoundRect(x, y, w, h, getArcWidth(), getArcHeight());
    }
    
    public boolean contains(double x, double y) {
        if (isEmpty()) {
            return false;
        }
        double rrx0 = getX();
        double rry0 = getY();
        double rrx1 = rrx0 + getWidth();
        double rry1 = rry0 + getHeight();
        if (x < rrx0 || y < rry0 || x >= rrx1 || y >= rry1) {
            return false;
        }
        double aw = Math.min(getWidth(), Math.abs(getArcWidth())) / 2.0;
        double ah = Math.min(getHeight(), Math.abs(getArcHeight())) / 2.0;
        if (x >= (rrx0 += aw) && x < (rrx0 = rrx1 - aw)) {
            return true;
        }
        if (y >= (rry0 += ah) && y < (rry0 = rry1 - ah)) {
            return true;
        }
        x = (x - rrx0) / aw;
        y = (y - rry0) / ah;
        return (x * x + y * y <= 1.0);
    }
    
    private int classify(double coord, double left, double right, double arcsize) {
        if (coord < left) {
            return 0;
        } else if (coord < left + arcsize) {
            return 1;
        } else if (coord < right - arcsize) {
            return 2;
        } else if (coord < right) {
            return 3;
        } else {
            return 4;
        }
    }
    
    public boolean intersects(double x, double y, double w, double h) {
        if (isEmpty() || w <= 0 || h <= 0) {
            return false;
        }
        double rrx0 = getX();
        double rry0 = getY();
        double rrx1 = rrx0 + getWidth();
        double rry1 = rry0 + getHeight();
        if (x + w <= rrx0 || x >= rrx1 || y + h <= rry0 || y >= rry1) {
            return false;
        }
        double aw = Math.min(getWidth(), Math.abs(getArcWidth())) / 2.0;
        double ah = Math.min(getHeight(), Math.abs(getArcHeight())) / 2.0;
        int x0class = classify(x, rrx0, rrx1, aw);
        int x1class = classify(x + w, rrx0, rrx1, aw);
        int y0class = classify(y, rry0, rry1, ah);
        int y1class = classify(y + h, rry0, rry1, ah);
        if (x0class == 2 || x1class == 2 || y0class == 2 || y1class == 2) {
            return true;
        }
        if ((x0class < 2 && x1class > 2) || (y0class < 2 && y1class > 2)) {
            return true;
        }
        x = (x1class == 1) ? (x = x + w - (rrx0 + aw)) : (x = x - (rrx1 - aw));
        y = (y1class == 1) ? (y = y + h - (rry0 + ah)) : (y = y - (rry1 - ah));
        x = x / aw;
        y = y / ah;
        return (x * x + y * y <= 1.0);
    }
    
    public boolean contains(double x, double y, double w, double h) {
        if (isEmpty() || w <= 0 || h <= 0) {
            return false;
        }
        return (contains(x, y) && contains(x + w, y) && contains(x, y + h) && contains(x + w, y + h));
    }
    
    public PathIterator getPathIterator(AffineTransform at) {
        return new RoundRectIterator(this, at);
    }
}
