package java.awt.geom;

public class Arc2D$Float extends Arc2D {
    public float x;
    public float y;
    public float width;
    public float height;
    public float start;
    public float extent;
    
    public Arc2D$Float() {
        super(OPEN);
    }
    
    public Arc2D$Float(int type) {
        super(type);
    }
    
    public Arc2D$Float(float x, float y, float w, float h, float start, float extent, int type) {
        super(type);
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
        this.start = start;
        this.extent = extent;
    }
    
    public Arc2D$Float(Rectangle2D ellipseBounds, float start, float extent, int type) {
        super(type);
        this.x = (float)ellipseBounds.getX();
        this.y = (float)ellipseBounds.getY();
        this.width = (float)ellipseBounds.getWidth();
        this.height = (float)ellipseBounds.getHeight();
        this.start = start;
        this.extent = extent;
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
    
    public double getAngleStart() {
        return (double)start;
    }
    
    public double getAngleExtent() {
        return (double)extent;
    }
    
    public boolean isEmpty() {
        return (width <= 0.0 || height <= 0.0);
    }
    
    public void setArc(double x, double y, double w, double h, double angSt, double angExt, int closure) {
        this.setArcType(closure);
        this.x = (float)x;
        this.y = (float)y;
        this.width = (float)w;
        this.height = (float)h;
        this.start = (float)angSt;
        this.extent = (float)angExt;
    }
    
    public void setAngleStart(double angSt) {
        this.start = (float)angSt;
    }
    
    public void setAngleExtent(double angExt) {
        this.extent = (float)angExt;
    }
    
    protected Rectangle2D makeBounds(double x, double y, double w, double h) {
        return new Rectangle2D$Float((float)x, (float)y, (float)w, (float)h);
    }
}
