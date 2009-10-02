package java.awt.geom;

public class RoundRectangle2D$Double extends RoundRectangle2D {
    public double x;
    public double y;
    public double width;
    public double height;
    public double arcwidth;
    public double archeight;
    
    public RoundRectangle2D$Double() {
        
    }
    
    public RoundRectangle2D$Double(double x, double y, double w, double h, double arcw, double arch) {
        
        setRoundRect(x, y, w, h, arcw, arch);
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
    
    public double getArcWidth() {
        return arcwidth;
    }
    
    public double getArcHeight() {
        return archeight;
    }
    
    public boolean isEmpty() {
        return (width <= 0.0F) || (height <= 0.0F);
    }
    
    public void setRoundRect(double x, double y, double w, double h, double arcw, double arch) {
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
        this.arcwidth = arcw;
        this.archeight = arch;
    }
    
    public void setRoundRect(RoundRectangle2D rr) {
        this.x = rr.getX();
        this.y = rr.getY();
        this.width = rr.getWidth();
        this.height = rr.getHeight();
        this.arcwidth = rr.getArcWidth();
        this.archeight = rr.getArcHeight();
    }
    
    public Rectangle2D getBounds2D() {
        return new Rectangle2D$Double(x, y, width, height);
    }
}
