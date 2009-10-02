package java.awt.geom;

public abstract class Dimension2D implements Cloneable {
    
    protected Dimension2D() {
        
    }
    
    public abstract double getWidth();
    
    public abstract double getHeight();
    
    public abstract void setSize(double width, double height);
    
    public void setSize(Dimension2D d) {
        setSize(d.getWidth(), d.getHeight());
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
}
