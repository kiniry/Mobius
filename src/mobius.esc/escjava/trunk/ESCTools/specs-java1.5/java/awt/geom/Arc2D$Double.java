package java.awt.geom;

public class Arc2D$Double extends Arc2D {
    public double x;
    public double y;
    public double width;
    public double height;
    public double start;
    public double extent;
    
    public Arc2D$Double() {
        super(OPEN);
    }
    
    public Arc2D$Double(int type) {
        super(type);
    }
    
    public Arc2D$Double(double x, double y, double w, double h, double start, double extent, int type) {
        super(type);
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
        this.start = start;
        this.extent = extent;
    }
    
    public Arc2D$Double(Rectangle2D ellipseBounds, double start, double extent, int type) {
        super(type);
        this.x = ellipseBounds.getX();
        this.y = ellipseBounds.getY();
        this.width = ellipseBounds.getWidth();
        this.height = ellipseBounds.getHeight();
        this.start = start;
        this.extent = extent;
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
    
    public double getAngleStart() {
        return start;
    }
    
    public double getAngleExtent() {
        return extent;
    }
    
    public boolean isEmpty() {
        return (width <= 0.0 || height <= 0.0);
    }
    
    public void setArc(double x, double y, double w, double h, double angSt, double angExt, int closure) {
        this.setArcType(closure);
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
        this.start = angSt;
        this.extent = angExt;
    }
    
    public void setAngleStart(double angSt) {
        this.start = angSt;
    }
    
    public void setAngleExtent(double angExt) {
        this.extent = angExt;
    }
    
    protected Rectangle2D makeBounds(double x, double y, double w, double h) {
        return new Rectangle2D$Double(x, y, w, h);
    }
}
