package java.awt;

import java.awt.geom.GeneralPath;
import sun.dc.path.FastPathProducer;
import sun.dc.path.PathConsumer;
import sun.dc.path.PathException;

class BasicStroke$FillAdapter implements PathConsumer {
    /*synthetic*/ final BasicStroke this$0;
    boolean closed;
    GeneralPath path;
    
    public BasicStroke$FillAdapter(/*synthetic*/ final BasicStroke this$0) {
        this.this$0 = this$0;
        
        path = new GeneralPath(GeneralPath.WIND_NON_ZERO);
    }
    
    public Shape getShape() {
        return path;
    }
    
    public void dispose() {
    }
    
    public PathConsumer getConsumer() {
        return null;
    }
    
    public void beginPath() {
    }
    
    public void beginSubpath(float x0, float y0) {
        if (closed) {
            path.closePath();
            closed = false;
        }
        path.moveTo(x0, y0);
    }
    
    public void appendLine(float x1, float y1) {
        path.lineTo(x1, y1);
    }
    
    public void appendQuadratic(float xm, float ym, float x1, float y1) {
        path.quadTo(xm, ym, x1, y1);
    }
    
    public void appendCubic(float xm, float ym, float xn, float yn, float x1, float y1) {
        path.curveTo(xm, ym, xn, yn, x1, y1);
    }
    
    public void closedSubpath() {
        closed = true;
    }
    
    public void endPath() {
        if (closed) {
            path.closePath();
            closed = false;
        }
    }
    
    public void useProxy(FastPathProducer proxy) throws PathException {
        proxy.sendTo(this);
    }
    
    public long getCPathConsumer() {
        return 0;
    }
}
