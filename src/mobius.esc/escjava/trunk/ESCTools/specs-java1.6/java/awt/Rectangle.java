package java.awt;

import java.awt.geom.Rectangle2D;

public class Rectangle extends Rectangle2D implements Shape, java.io.Serializable {
    public int x;
    public int y;
    public int width;
    public int height;
    private static final long serialVersionUID = -4345857070255674764L;
    
    private static native void initIDs();
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    public Rectangle() {
        this(0, 0, 0, 0);
    }
    
    public Rectangle(Rectangle r) {
        this(r.x, r.y, r.width, r.height);
    }
    
    public Rectangle(int x, int y, int width, int height) {
        
        this.x = x;
        this.y = y;
        this.width = width;
        this.height = height;
    }
    
    public Rectangle(int width, int height) {
        this(0, 0, width, height);
    }
    
    public Rectangle(Point p, Dimension d) {
        this(p.x, p.y, d.width, d.height);
    }
    
    public Rectangle(Point p) {
        this(p.x, p.y, 0, 0);
    }
    
    public Rectangle(Dimension d) {
        this(0, 0, d.width, d.height);
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
    
    public Rectangle getBounds() {
        return new Rectangle(x, y, width, height);
    }
    
    public Rectangle2D getBounds2D() {
        return new Rectangle(x, y, width, height);
    }
    
    public void setBounds(Rectangle r) {
        setBounds(r.x, r.y, r.width, r.height);
    }
    
    public void setBounds(int x, int y, int width, int height) {
        reshape(x, y, width, height);
    }
    
    public void setRect(double x, double y, double width, double height) {
        int x0 = (int)Math.floor(x);
        int y0 = (int)Math.floor(y);
        int x1 = (int)Math.ceil(x + width);
        int y1 = (int)Math.ceil(y + height);
        setBounds(x0, y0, x1 - x0, y1 - y0);
    }
    
    
    public void reshape(int x, int y, int width, int height) {
        this.x = x;
        this.y = y;
        this.width = width;
        this.height = height;
    }
    
    public Point getLocation() {
        return new Point(x, y);
    }
    
    public void setLocation(Point p) {
        setLocation(p.x, p.y);
    }
    
    public void setLocation(int x, int y) {
        move(x, y);
    }
    
    
    public void move(int x, int y) {
        this.x = x;
        this.y = y;
    }
    
    public void translate(int x, int y) {
        this.x += x;
        this.y += y;
    }
    
    public Dimension getSize() {
        return new Dimension(width, height);
    }
    
    public void setSize(Dimension d) {
        setSize(d.width, d.height);
    }
    
    public void setSize(int width, int height) {
        resize(width, height);
    }
    
    
    public void resize(int width, int height) {
        this.width = width;
        this.height = height;
    }
    
    public boolean contains(Point p) {
        return contains(p.x, p.y);
    }
    
    public boolean contains(int x, int y) {
        return inside(x, y);
    }
    
    public boolean contains(Rectangle r) {
        return contains(r.x, r.y, r.width, r.height);
    }
    
    public boolean contains(int X, int Y, int W, int H) {
        int w = this.width;
        int h = this.height;
        if ((w | h | W | H) < 0) {
            return false;
        }
        int x = this.x;
        int y = this.y;
        if (X < x || Y < y) {
            return false;
        }
        w += x;
        W += X;
        if (W <= X) {
            if (w >= x || W > w) return false;
        } else {
            if (w >= x && W > w) return false;
        }
        h += y;
        H += Y;
        if (H <= Y) {
            if (h >= y || H > h) return false;
        } else {
            if (h >= y && H > h) return false;
        }
        return true;
    }
    
    
    public boolean inside(int X, int Y) {
        int w = this.width;
        int h = this.height;
        if ((w | h) < 0) {
            return false;
        }
        int x = this.x;
        int y = this.y;
        if (X < x || Y < y) {
            return false;
        }
        w += x;
        h += y;
        return ((w < x || w > X) && (h < y || h > Y));
    }
    
    public boolean intersects(Rectangle r) {
        int tw = this.width;
        int th = this.height;
        int rw = r.width;
        int rh = r.height;
        if (rw <= 0 || rh <= 0 || tw <= 0 || th <= 0) {
            return false;
        }
        int tx = this.x;
        int ty = this.y;
        int rx = r.x;
        int ry = r.y;
        rw += rx;
        rh += ry;
        tw += tx;
        th += ty;
        return ((rw < rx || rw > tx) && (rh < ry || rh > ty) && (tw < tx || tw > rx) && (th < ty || th > ry));
    }
    
    public Rectangle intersection(Rectangle r) {
        int tx1 = this.x;
        int ty1 = this.y;
        int rx1 = r.x;
        int ry1 = r.y;
        long tx2 = tx1;
        tx2 += this.width;
        long ty2 = ty1;
        ty2 += this.height;
        long rx2 = rx1;
        rx2 += r.width;
        long ry2 = ry1;
        ry2 += r.height;
        if (tx1 < rx1) tx1 = rx1;
        if (ty1 < ry1) ty1 = ry1;
        if (tx2 > rx2) tx2 = rx2;
        if (ty2 > ry2) ty2 = ry2;
        tx2 -= tx1;
        ty2 -= ty1;
        if (tx2 < Integer.MIN_VALUE) tx2 = Integer.MIN_VALUE;
        if (ty2 < Integer.MIN_VALUE) ty2 = Integer.MIN_VALUE;
        return new Rectangle(tx1, ty1, (int)tx2, (int)ty2);
    }
    
    public Rectangle union(Rectangle r) {
        int x1 = Math.min(x, r.x);
        int x2 = Math.max(x + width, r.x + r.width);
        int y1 = Math.min(y, r.y);
        int y2 = Math.max(y + height, r.y + r.height);
        return new Rectangle(x1, y1, x2 - x1, y2 - y1);
    }
    
    public void add(int newx, int newy) {
        int x1 = Math.min(x, newx);
        int x2 = Math.max(x + width, newx);
        int y1 = Math.min(y, newy);
        int y2 = Math.max(y + height, newy);
        x = x1;
        y = y1;
        width = x2 - x1;
        height = y2 - y1;
    }
    
    public void add(Point pt) {
        add(pt.x, pt.y);
    }
    
    public void add(Rectangle r) {
        int x1 = Math.min(x, r.x);
        int x2 = Math.max(x + width, r.x + r.width);
        int y1 = Math.min(y, r.y);
        int y2 = Math.max(y + height, r.y + r.height);
        x = x1;
        y = y1;
        width = x2 - x1;
        height = y2 - y1;
    }
    
    public void grow(int h, int v) {
        x -= h;
        y -= v;
        width += h * 2;
        height += v * 2;
    }
    
    public boolean isEmpty() {
        return (width <= 0) || (height <= 0);
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
    
    public Rectangle2D createIntersection(Rectangle2D r) {
        if (r instanceof Rectangle) {
            return intersection((Rectangle)(Rectangle)r);
        }
        Rectangle2D dest = new Rectangle2D$Double();
        Rectangle2D.intersect(this, r, dest);
        return dest;
    }
    
    public Rectangle2D createUnion(Rectangle2D r) {
        if (r instanceof Rectangle) {
            return union((Rectangle)(Rectangle)r);
        }
        Rectangle2D dest = new Rectangle2D$Double();
        Rectangle2D.union(this, r, dest);
        return dest;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Rectangle) {
            Rectangle r = (Rectangle)(Rectangle)obj;
            return ((x == r.x) && (y == r.y) && (width == r.width) && (height == r.height));
        }
        return super.equals(obj);
    }
    
    public String toString() {
        return getClass().getName() + "[x=" + x + ",y=" + y + ",width=" + width + ",height=" + height + "]";
    }
}
