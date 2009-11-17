package java.awt;

import java.awt.geom.AffineTransform;
import java.awt.geom.PathIterator;

class Polygon$PolygonPathIterator implements PathIterator {
    /*synthetic*/ final Polygon this$0;
    Polygon poly;
    AffineTransform transform;
    int index;
    
    public Polygon$PolygonPathIterator(/*synthetic*/ final Polygon this$0, Polygon pg, AffineTransform at) {
        this.this$0 = this$0;
        
        poly = pg;
        transform = at;
        if (pg.npoints == 0) {
            index = 1;
        }
    }
    
    public int getWindingRule() {
        return WIND_EVEN_ODD;
    }
    
    public boolean isDone() {
        return index > poly.npoints;
    }
    
    public void next() {
        index++;
    }
    
    public int currentSegment(float[] coords) {
        if (index >= poly.npoints) {
            return SEG_CLOSE;
        }
        coords[0] = poly.xpoints[index];
        coords[1] = poly.ypoints[index];
        if (transform != null) {
            transform.transform(coords, 0, coords, 0, 1);
        }
        return (index == 0 ? SEG_MOVETO : SEG_LINETO);
    }
    
    public int currentSegment(double[] coords) {
        if (index >= poly.npoints) {
            return SEG_CLOSE;
        }
        coords[0] = poly.xpoints[index];
        coords[1] = poly.ypoints[index];
        if (transform != null) {
            transform.transform(coords, 0, coords, 0, 1);
        }
        return (index == 0 ? SEG_MOVETO : SEG_LINETO);
    }
}
