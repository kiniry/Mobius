package java.awt.geom;

import java.util.*;

class QuadIterator implements PathIterator {
    QuadCurve2D quad;
    AffineTransform affine;
    int index;
    
    QuadIterator(QuadCurve2D q, AffineTransform at) {
        
        this.quad = q;
        this.affine = at;
    }
    
    public int getWindingRule() {
        return WIND_NON_ZERO;
    }
    
    public boolean isDone() {
        return (index > 1);
    }
    
    public void next() {
        index++;
    }
    
    public int currentSegment(float[] coords) {
        if (isDone()) {
            throw new NoSuchElementException("quad iterator iterator out of bounds");
        }
        int type;
        if (index == 0) {
            coords[0] = (float)quad.getX1();
            coords[1] = (float)quad.getY1();
            type = SEG_MOVETO;
        } else {
            coords[0] = (float)quad.getCtrlX();
            coords[1] = (float)quad.getCtrlY();
            coords[2] = (float)quad.getX2();
            coords[3] = (float)quad.getY2();
            type = SEG_QUADTO;
        }
        if (affine != null) {
            affine.transform(coords, 0, coords, 0, index == 0 ? 1 : 2);
        }
        return type;
    }
    
    public int currentSegment(double[] coords) {
        if (isDone()) {
            throw new NoSuchElementException("quad iterator iterator out of bounds");
        }
        int type;
        if (index == 0) {
            coords[0] = quad.getX1();
            coords[1] = quad.getY1();
            type = SEG_MOVETO;
        } else {
            coords[0] = quad.getCtrlX();
            coords[1] = quad.getCtrlY();
            coords[2] = quad.getX2();
            coords[3] = quad.getY2();
            type = SEG_QUADTO;
        }
        if (affine != null) {
            affine.transform(coords, 0, coords, 0, index == 0 ? 1 : 2);
        }
        return type;
    }
}
