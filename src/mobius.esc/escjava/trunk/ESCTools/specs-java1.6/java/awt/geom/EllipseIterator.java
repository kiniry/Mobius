package java.awt.geom;

import java.util.*;

class EllipseIterator implements PathIterator {
    double x;
    double y;
    double w;
    double h;
    AffineTransform affine;
    int index;
    
    EllipseIterator(Ellipse2D e, AffineTransform at) {
        
        this.x = e.getX();
        this.y = e.getY();
        this.w = e.getWidth();
        this.h = e.getHeight();
        this.affine = at;
        if (w < 0 || h < 0) {
            index = 6;
        }
    }
    
    public int getWindingRule() {
        return WIND_NON_ZERO;
    }
    
    public boolean isDone() {
        return index > 5;
    }
    
    public void next() {
        index++;
    }
    public static final double CtrlVal = 0.5522847498307933;
    private static final double pcv = 0.5 + CtrlVal * 0.5;
    private static final double ncv = 0.5 - CtrlVal * 0.5;
    private static double[][] ctrlpts = {{1.0, pcv, pcv, 1.0, 0.5, 1.0}, {ncv, 1.0, 0.0, pcv, 0.0, 0.5}, {0.0, ncv, ncv, 0.0, 0.5, 0.0}, {pcv, 0.0, 1.0, ncv, 1.0, 0.5}};
    
    public int currentSegment(float[] coords) {
        if (isDone()) {
            throw new NoSuchElementException("ellipse iterator out of bounds");
        }
        if (index == 5) {
            return SEG_CLOSE;
        }
        if (index == 0) {
            double[] ctrls = ctrlpts[3];
            coords[0] = (float)(x + ctrls[4] * w);
            coords[1] = (float)(y + ctrls[5] * h);
            if (affine != null) {
                affine.transform(coords, 0, coords, 0, 1);
            }
            return SEG_MOVETO;
        }
        double[] ctrls = ctrlpts[index - 1];
        coords[0] = (float)(x + ctrls[0] * w);
        coords[1] = (float)(y + ctrls[1] * h);
        coords[2] = (float)(x + ctrls[2] * w);
        coords[3] = (float)(y + ctrls[3] * h);
        coords[4] = (float)(x + ctrls[4] * w);
        coords[5] = (float)(y + ctrls[5] * h);
        if (affine != null) {
            affine.transform(coords, 0, coords, 0, 3);
        }
        return SEG_CUBICTO;
    }
    
    public int currentSegment(double[] coords) {
        if (isDone()) {
            throw new NoSuchElementException("ellipse iterator out of bounds");
        }
        if (index == 5) {
            return SEG_CLOSE;
        }
        if (index == 0) {
            double[] ctrls = ctrlpts[3];
            coords[0] = x + ctrls[4] * w;
            coords[1] = y + ctrls[5] * h;
            if (affine != null) {
                affine.transform(coords, 0, coords, 0, 1);
            }
            return SEG_MOVETO;
        }
        double[] ctrls = ctrlpts[index - 1];
        coords[0] = x + ctrls[0] * w;
        coords[1] = y + ctrls[1] * h;
        coords[2] = x + ctrls[2] * w;
        coords[3] = y + ctrls[3] * h;
        coords[4] = x + ctrls[4] * w;
        coords[5] = y + ctrls[5] * h;
        if (affine != null) {
            affine.transform(coords, 0, coords, 0, 3);
        }
        return SEG_CUBICTO;
    }
}
