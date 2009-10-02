package java.awt.geom;

public class RoundRectangle2D$Float extends RoundRectangle2D {
    public float x;
    public float y;
    public float width;
    public float height;
    public float arcwidth;
    public float archeight;
    
    public RoundRectangle2D$Float() {
        
    }
    
    public RoundRectangle2D$Float(float x, float y, float w, float h, float arcw, float arch) {
        
        setRoundRect(x, y, w, h, arcw, arch);
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
    
    public double getArcWidth() {
        return (double)arcwidth;
    }
    
    public double getArcHeight() {
        return (double)archeight;
    }
    
    public boolean isEmpty() {
        return (width <= 0.0F) || (height <= 0.0F);
    }
    
    public void setRoundRect(float x, float y, float w, float h, float arcw, float arch) {
        this.x = x;
        this.y = y;
        this.width = w;
        this.height = h;
        this.arcwidth = arcw;
        this.archeight = arch;
    }
    
    public void setRoundRect(double x, double y, double w, double h, double arcw, double arch) {
        this.x = (float)x;
        this.y = (float)y;
        this.width = (float)w;
        this.height = (float)h;
        this.arcwidth = (float)arcw;
        this.archeight = (float)arch;
    }
    
    public void setRoundRect(RoundRectangle2D rr) {
        this.x = (float)rr.getX();
        this.y = (float)rr.getY();
        this.width = (float)rr.getWidth();
        this.height = (float)rr.getHeight();
        this.arcwidth = (float)rr.getArcWidth();
        this.archeight = (float)rr.getArcHeight();
    }
    
    public Rectangle2D getBounds2D() {
        return new Rectangle2D$Float(x, y, width, height);
    }
}
