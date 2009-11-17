package java.awt;

public abstract class PrintJob {
    
    public PrintJob() {
        
    }
    
    public abstract Graphics getGraphics();
    
    public abstract Dimension getPageDimension();
    
    public abstract int getPageResolution();
    
    public abstract boolean lastPageFirst();
    
    public abstract void end();
    
    public void finalize() {
        end();
    }
}
