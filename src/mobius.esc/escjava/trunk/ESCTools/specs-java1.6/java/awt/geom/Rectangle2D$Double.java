package java.awt.geom;

public class Rectangle2D$Double extends Rectangle2D {
    public double x;
    public double y;
    public double width;
    public double height;
    
    public Rectangle2D$Double() {
        
    }
    
    public Rectangle2D$Double(double x, double y, double w, double h) {
        
        setRect(x, y, w, h);
    }
    
    public double getX() {
        return x;
    }
    
    public double getY() {
        return y;
    }
    
    public double getWidth() {
        return width;
    }
    
    public double getHeight() {
        return height;
    }
    
    public boolean isEmpty() {
        return (width <= 0.0) || (height <= 0.0);
    }
    
    public void setRect(double x, double y, double w, double h) {
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
    }
    
    public void setRect(Rectangle2D r) {
        this.x = r.getX();
        this.y = r.getY();
        this.width = r.getWidth();
        this.height = r.getHeight();
    }
    
    public int outcode(double x, double y) {
        int out = 0;
        if (this.width <= 0) {
            out |= OUT_LEFT | OUT_RIGHT;
        } else if (x < this.x) {
            out |= OUT_LEFT;
        } else if (x > this.x + this.width) {
            out |= OUT_RIGHT;
        }
        if (this.height <= 0) {
            out |= OUT_TOP | OUT_BOTTOM;
        } else if (y < this.y) {
            out |= OUT_TOP;
        } else if (y > this.y + this.height) {
            out |= OUT_BOTTOM;
        }
        return out;
    }
    
    public Rectangle2D getBounds2D() {
        return new Rectangle2D$Double(x, y, width, height);
    }
    
    public Rectangle2D createIntersection(Rectangle2D r) {
        Rectangle2D dest = new Rectangle2D$Double();
        Rectangle2D.intersect(this, r, dest);
        return dest;
    }
    
    public Rectangle2D createUnion(Rectangle2D r) {
        Rectangle2D dest = new Rectangle2D$Double();
        Rectangle2D.union(this, r, dest);
        return dest;
    }
    
    public String toString() {
        return getClass().getName() + "[x=" + x + ",y=" + y + ",w=" + width + ",h=" + height + "]";
    }
}
