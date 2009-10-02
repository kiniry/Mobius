package java.awt.geom;

public class Rectangle2D$Float extends Rectangle2D {
    public float x;
    public float y;
    public float width;
    public float height;
    
    public Rectangle2D$Float() {
        
    }
    
    public Rectangle2D$Float(float x, float y, float w, float h) {
        
        setRect(x, y, w, h);
    }
    
    public double getX() {
        return (double)x;
    }
    
    public double getY() {
        return (double)y;
    }
    
    public double getWidth() {
        return (double)width;
    }
    
    public double getHeight() {
        return (double)height;
    }
    
    public boolean isEmpty() {
        return (width <= 0.0F) || (height <= 0.0F);
    }
    
    public void setRect(float x, float y, float w, float h) {
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
    }
    
    public void setRect(double x, double y, double w, double h) {
        this.x = (float)x;
        this.y = (float)y;
        this.width = (float)w;
        this.height = (float)h;
    }
    
    public void setRect(Rectangle2D r) {
        this.x = (float)r.getX();
        this.y = (float)r.getY();
        this.width = (float)r.getWidth();
        this.height = (float)r.getHeight();
    }
    
    public int outcode(double x, double y) {
        int out = 0;
        if (this.width <= 0) {
            out |= OUT_LEFT | OUT_RIGHT;
        } else if (x < this.x) {
            out |= OUT_LEFT;
        } else if (x > this.x + (double)this.width) {
            out |= OUT_RIGHT;
        }
        if (this.height <= 0) {
            out |= OUT_TOP | OUT_BOTTOM;
        } else if (y < this.y) {
            out |= OUT_TOP;
        } else if (y > this.y + (double)this.height) {
            out |= OUT_BOTTOM;
        }
        return out;
    }
    
    public Rectangle2D getBounds2D() {
        return new Rectangle2D$Float(x, y, width, height);
    }
    
    public Rectangle2D createIntersection(Rectangle2D r) {
        Rectangle2D dest;
        if (r instanceof Rectangle2D$Float) {
            dest = new Rectangle2D$Float();
        } else {
            dest = new Rectangle2D$Double();
        }
        Rectangle2D.intersect(this, r, dest);
        return dest;
    }
    
    public Rectangle2D createUnion(Rectangle2D r) {
        Rectangle2D dest;
        if (r instanceof Rectangle2D$Float) {
            dest = new Rectangle2D$Float();
        } else {
            dest = new Rectangle2D$Double();
        }
        Rectangle2D.union(this, r, dest);
        return dest;
    }
    
    public String toString() {
        return getClass().getName() + "[x=" + x + ",y=" + y + ",w=" + width + ",h=" + height + "]";
    }
}
