package java.awt.geom;

import java.util.*;

class RoundRectIterator implements PathIterator {
    double x;
    double y;
    double w;
    double h;
    double aw;
    double ah;
    AffineTransform affine;
    int index;
    
    RoundRectIterator(RoundRectangle2D rr, AffineTransform at) {
        
        this.x = rr.getX();
        this.y = rr.getY();
        this.w = rr.getWidth();
        this.h = rr.getHeight();
        this.aw = Math.min(w, Math.abs(rr.getArcWidth()));
        this.ah = Math.min(h, Math.abs(rr.getArcHeight()));
        this.affine = at;
        if (aw < 0 || ah < 0) {
            index = ctrlpts.length;
        }
    }
    
    public int getWindingRule() {
        return WIND_NON_ZERO;
    }
    
    public boolean isDone() {
        return index >= ctrlpts.length;
    }
    
    public void next() {
        index++;
    }
    private static final double angle = Math.PI / 4.0;
    private static final double a = 1.0 - Math.cos(angle);
    private static final double b = Math.tan(angle);
    private static final double c = Math.sqrt(1.0 + b * b) - 1 + a;
    private static final double cv = 4.0 / 3.0 * a * b / c;
    private static final double acv = (1.0 - cv) / 2.0;
    private static double[][] ctrlpts = {{0.0, 0.0, 0.0, 0.5}, {0.0, 0.0, 1.0, -0.5}, {0.0, 0.0, 1.0, -acv, 0.0, acv, 1.0, 0.0, 0.0, 0.5, 1.0, 0.0}, {1.0, -0.5, 1.0, 0.0}, {1.0, -acv, 1.0, 0.0, 1.0, 0.0, 1.0, -acv, 1.0, 0.0, 1.0, -0.5}, {1.0, 0.0, 0.0, 0.5}, {1.0, 0.0, 0.0, acv, 1.0, -acv, 0.0, 0.0, 1.0, -0.5, 0.0, 0.0}, {0.0, 0.5, 0.0, 0.0}, {0.0, acv, 0.0, 0.0, 0.0, 0.0, 0.0, acv, 0.0, 0.0, 0.0, 0.5}, {}};
    private static int[] types = {SEG_MOVETO, SEG_LINETO, SEG_CUBICTO, SEG_LINETO, SEG_CUBICTO, SEG_LINETO, SEG_CUBICTO, SEG_LINETO, SEG_CUBICTO, SEG_CLOSE};
    
    public int currentSegment(float[] coords) {
        if (isDone()) {
            throw new NoSuchElementException("roundrect iterator out of bounds");
        }
        double[] ctrls = ctrlpts[index];
        int nc = 0;
        for (int i = 0; i < ctrls.length; i += 4) {
            coords[nc++] = (float)(x + ctrls[i + 0] * w + ctrls[i + 1] * aw);
            coords[nc++] = (float)(y + ctrls[i + 2] * h + ctrls[i + 3] * ah);
        }
        if (affine != null) {
            affine.transform(coords, 0, coords, 0, nc / 2);
        }
        return types[index];
    }
    
    public int currentSegment(double[] coords) {
        if (isDone()) {
            throw new NoSuchElementException("roundrect iterator out of bounds");
        }
        double[] ctrls = ctrlpts[index];
        int nc = 0;
        for (int i = 0; i < ctrls.length; i += 4) {
            coords[nc++] = (x + ctrls[i + 0] * w + ctrls[i + 1] * aw);
            coords[nc++] = (y + ctrls[i + 2] * h + ctrls[i + 3] * ah);
        }
        if (affine != null) {
            affine.transform(coords, 0, coords, 0, nc / 2);
        }
        return types[index];
    }
}
