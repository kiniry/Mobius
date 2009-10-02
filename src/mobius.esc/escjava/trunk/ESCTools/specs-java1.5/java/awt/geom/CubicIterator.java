package java.awt.geom;

import java.util.*;

class CubicIterator implements PathIterator {
    CubicCurve2D cubic;
    AffineTransform affine;
    int index;
    
    CubicIterator(CubicCurve2D q, AffineTransform at) {
        
        this.cubic = q;
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
            throw new NoSuchElementException("cubic iterator iterator out of bounds");
        }
        int type;
        if (index == 0) {
            coords[0] = (float)cubic.getX1();
            coords[1] = (float)cubic.getY1();
            type = SEG_MOVETO;
        } else {
            coords[0] = (float)cubic.getCtrlX1();
            coords[1] = (float)cubic.getCtrlY1();
            coords[2] = (float)cubic.getCtrlX2();
            coords[3] = (float)cubic.getCtrlY2();
            coords[4] = (float)cubic.getX2();
            coords[5] = (float)cubic.getY2();
            type = SEG_CUBICTO;
        }
        if (affine != null) {
            affine.transform(coords, 0, coords, 0, index == 0 ? 1 : 3);
        }
        return type;
    }
    
    public int currentSegment(double[] coords) {
        if (isDone()) {
            throw new NoSuchElementException("cubic iterator iterator out of bounds");
        }
        int type;
        if (index == 0) {
            coords[0] = cubic.getX1();
            coords[1] = cubic.getY1();
            type = SEG_MOVETO;
        } else {
            coords[0] = cubic.getCtrlX1();
            coords[1] = cubic.getCtrlY1();
            coords[2] = cubic.getCtrlX2();
            coords[3] = cubic.getCtrlY2();
            coords[4] = cubic.getX2();
            coords[5] = cubic.getY2();
            type = SEG_CUBICTO;
        }
        if (affine != null) {
            affine.transform(coords, 0, coords, 0, index == 0 ? 1 : 3);
        }
        return type;
    }
}
