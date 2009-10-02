package java.awt.geom;

import java.awt.Shape;
import java.awt.Rectangle;
import java.util.Arrays;

public abstract class CubicCurve2D implements Shape, Cloneable {
    {
    }
    {
    }
    
    protected CubicCurve2D() {
        
    }
    
    public abstract double getX1();
    
    public abstract double getY1();
    
    public abstract Point2D getP1();
    
    public abstract double getCtrlX1();
    
    public abstract double getCtrlY1();
    
    public abstract Point2D getCtrlP1();
    
    public abstract double getCtrlX2();
    
    public abstract double getCtrlY2();
    
    public abstract Point2D getCtrlP2();
    
    public abstract double getX2();
    
    public abstract double getY2();
    
    public abstract Point2D getP2();
    
    public abstract void setCurve(double x1, double y1, double ctrlx1, double ctrly1, double ctrlx2, double ctrly2, double x2, double y2);
    
    public void setCurve(double[] coords, int offset) {
        setCurve(coords[offset + 0], coords[offset + 1], coords[offset + 2], coords[offset + 3], coords[offset + 4], coords[offset + 5], coords[offset + 6], coords[offset + 7]);
    }
    
    public void setCurve(Point2D p1, Point2D cp1, Point2D cp2, Point2D p2) {
        setCurve(p1.getX(), p1.getY(), cp1.getX(), cp1.getY(), cp2.getX(), cp2.getY(), p2.getX(), p2.getY());
    }
    
    public void setCurve(Point2D[] pts, int offset) {
        setCurve(pts[offset + 0].getX(), pts[offset + 0].getY(), pts[offset + 1].getX(), pts[offset + 1].getY(), pts[offset + 2].getX(), pts[offset + 2].getY(), pts[offset + 3].getX(), pts[offset + 3].getY());
    }
    
    public void setCurve(CubicCurve2D c) {
        setCurve(c.getX1(), c.getY1(), c.getCtrlX1(), c.getCtrlY1(), c.getCtrlX2(), c.getCtrlY2(), c.getX2(), c.getY2());
    }
    
    public static double getFlatnessSq(double x1, double y1, double ctrlx1, double ctrly1, double ctrlx2, double ctrly2, double x2, double y2) {
        return Math.max(Line2D.ptSegDistSq(x1, y1, x2, y2, ctrlx1, ctrly1), Line2D.ptSegDistSq(x1, y1, x2, y2, ctrlx2, ctrly2));
    }
    
    public static double getFlatness(double x1, double y1, double ctrlx1, double ctrly1, double ctrlx2, double ctrly2, double x2, double y2) {
        return Math.sqrt(getFlatnessSq(x1, y1, ctrlx1, ctrly1, ctrlx2, ctrly2, x2, y2));
    }
    
    public static double getFlatnessSq(double[] coords, int offset) {
        return getFlatnessSq(coords[offset + 0], coords[offset + 1], coords[offset + 2], coords[offset + 3], coords[offset + 4], coords[offset + 5], coords[offset + 6], coords[offset + 7]);
    }
    
    public static double getFlatness(double[] coords, int offset) {
        return getFlatness(coords[offset + 0], coords[offset + 1], coords[offset + 2], coords[offset + 3], coords[offset + 4], coords[offset + 5], coords[offset + 6], coords[offset + 7]);
    }
    
    public double getFlatnessSq() {
        return getFlatnessSq(getX1(), getY1(), getCtrlX1(), getCtrlY1(), getCtrlX2(), getCtrlY2(), getX2(), getY2());
    }
    
    public double getFlatness() {
        return getFlatness(getX1(), getY1(), getCtrlX1(), getCtrlY1(), getCtrlX2(), getCtrlY2(), getX2(), getY2());
    }
    
    public void subdivide(CubicCurve2D left, CubicCurve2D right) {
        subdivide(this, left, right);
    }
    
    public static void subdivide(CubicCurve2D src, CubicCurve2D left, CubicCurve2D right) {
        double x1 = src.getX1();
        double y1 = src.getY1();
        double ctrlx1 = src.getCtrlX1();
        double ctrly1 = src.getCtrlY1();
        double ctrlx2 = src.getCtrlX2();
        double ctrly2 = src.getCtrlY2();
        double x2 = src.getX2();
        double y2 = src.getY2();
        double centerx = (ctrlx1 + ctrlx2) / 2.0;
        double centery = (ctrly1 + ctrly2) / 2.0;
        ctrlx1 = (x1 + ctrlx1) / 2.0;
        ctrly1 = (y1 + ctrly1) / 2.0;
        ctrlx2 = (x2 + ctrlx2) / 2.0;
        ctrly2 = (y2 + ctrly2) / 2.0;
        double ctrlx12 = (ctrlx1 + centerx) / 2.0;
        double ctrly12 = (ctrly1 + centery) / 2.0;
        double ctrlx21 = (ctrlx2 + centerx) / 2.0;
        double ctrly21 = (ctrly2 + centery) / 2.0;
        centerx = (ctrlx12 + ctrlx21) / 2.0;
        centery = (ctrly12 + ctrly21) / 2.0;
        if (left != null) {
            left.setCurve(x1, y1, ctrlx1, ctrly1, ctrlx12, ctrly12, centerx, centery);
        }
        if (right != null) {
            right.setCurve(centerx, centery, ctrlx21, ctrly21, ctrlx2, ctrly2, x2, y2);
        }
    }
    
    public static void subdivide(double[] src, int srcoff, double[] left, int leftoff, double[] right, int rightoff) {
        double x1 = src[srcoff + 0];
        double y1 = src[srcoff + 1];
        double ctrlx1 = src[srcoff + 2];
        double ctrly1 = src[srcoff + 3];
        double ctrlx2 = src[srcoff + 4];
        double ctrly2 = src[srcoff + 5];
        double x2 = src[srcoff + 6];
        double y2 = src[srcoff + 7];
        if (left != null) {
            left[leftoff + 0] = x1;
            left[leftoff + 1] = y1;
        }
        if (right != null) {
            right[rightoff + 6] = x2;
            right[rightoff + 7] = y2;
        }
        x1 = (x1 + ctrlx1) / 2.0;
        y1 = (y1 + ctrly1) / 2.0;
        x2 = (x2 + ctrlx2) / 2.0;
        y2 = (y2 + ctrly2) / 2.0;
        double centerx = (ctrlx1 + ctrlx2) / 2.0;
        double centery = (ctrly1 + ctrly2) / 2.0;
        ctrlx1 = (x1 + centerx) / 2.0;
        ctrly1 = (y1 + centery) / 2.0;
        ctrlx2 = (x2 + centerx) / 2.0;
        ctrly2 = (y2 + centery) / 2.0;
        centerx = (ctrlx1 + ctrlx2) / 2.0;
        centery = (ctrly1 + ctrly2) / 2.0;
        if (left != null) {
            left[leftoff + 2] = x1;
            left[leftoff + 3] = y1;
            left[leftoff + 4] = ctrlx1;
            left[leftoff + 5] = ctrly1;
            left[leftoff + 6] = centerx;
            left[leftoff + 7] = centery;
        }
        if (right != null) {
            right[rightoff + 0] = centerx;
            right[rightoff + 1] = centery;
            right[rightoff + 2] = ctrlx2;
            right[rightoff + 3] = ctrly2;
            right[rightoff + 4] = x2;
            right[rightoff + 5] = y2;
        }
    }
    
    public static int solveCubic(double[] eqn) {
        return solveCubic(eqn, eqn);
    }
    
    public static int solveCubic(double[] eqn, double[] res) {
        double d = eqn[3];
        if (d == 0.0) {
            return QuadCurve2D.solveQuadratic(eqn, res);
        }
        double a = eqn[2] / d;
        double b = eqn[1] / d;
        double c = eqn[0] / d;
        int roots = 0;
        double Q = (a * a - 3.0 * b) / 9.0;
        double R = (2.0 * a * a * a - 9.0 * a * b + 27.0 * c) / 54.0;
        double R2 = R * R;
        double Q3 = Q * Q * Q;
        a = a / 3.0;
        if (R2 < Q3) {
            double theta = Math.acos(R / Math.sqrt(Q3));
            Q = -2.0 * Math.sqrt(Q);
            if (res == eqn) {
                eqn = new double[4];
                System.arraycopy(res, 0, eqn, 0, 4);
            }
            res[roots++] = Q * Math.cos(theta / 3.0) - a;
            res[roots++] = Q * Math.cos((theta + Math.PI * 2.0) / 3.0) - a;
            res[roots++] = Q * Math.cos((theta - Math.PI * 2.0) / 3.0) - a;
            fixRoots(res, eqn);
        } else {
            boolean neg = (R < 0.0);
            double S = Math.sqrt(R2 - Q3);
            if (neg) {
                R = -R;
            }
            double A = Math.pow(R + S, 1.0 / 3.0);
            if (!neg) {
                A = -A;
            }
            double B = (A == 0.0) ? 0.0 : (Q / A);
            res[roots++] = (A + B) - a;
        }
        return roots;
    }
    
    private static void fixRoots(double[] res, double[] eqn) {
        final double EPSILON = 1.0E-5;
        for (int i = 0; i < 3; i++) {
            double t = res[i];
            if (Math.abs(t) < EPSILON) {
                res[i] = findZero(t, 0, eqn);
            } else if (Math.abs(t - 1) < EPSILON) {
                res[i] = findZero(t, 1, eqn);
            }
        }
    }
    
    private static double solveEqn(double[] eqn, int order, double t) {
        double v = eqn[order];
        while (--order >= 0) {
            v = v * t + eqn[order];
        }
        return v;
    }
    
    private static double findZero(double t, double target, double[] eqn) {
        double[] slopeqn = {eqn[1], 2 * eqn[2], 3 * eqn[3]};
        double slope;
        double origdelta = 0;
        double origt = t;
        while (true) {
            slope = solveEqn(slopeqn, 2, t);
            if (slope == 0) {
                return t;
            }
            double y = solveEqn(eqn, 3, t);
            if (y == 0) {
                return t;
            }
            double delta = -(y / slope);
            if (origdelta == 0) {
                origdelta = delta;
            }
            if (t < target) {
                if (delta < 0) return t;
            } else if (t > target) {
                if (delta > 0) return t;
            } else {
                return (delta > 0 ? (target + java.lang.Double.MIN_VALUE) : (target - java.lang.Double.MIN_VALUE));
            }
            double newt = t + delta;
            if (t == newt) {
                return t;
            }
            if (delta * origdelta < 0) {
                int tag = (origt < t ? getTag(target, origt, t) : getTag(target, t, origt));
                if (tag != INSIDE) {
                    return (origt + t) / 2;
                }
                t = target;
            } else {
                t = newt;
            }
        }
    }
    
    public boolean contains(double x, double y) {
        int crossings = 0;
        double x1 = getX1();
        double y1 = getY1();
        double x2 = getX2();
        double y2 = getY2();
        double dy = y2 - y1;
        if ((dy > 0.0 && y >= y1 && y <= y2) || (dy < 0.0 && y <= y1 && y >= y2)) {
            if (x < x1 + (y - y1) * (x2 - x1) / dy) {
                crossings++;
            }
        }
        double ctrlx1 = getCtrlX1();
        double ctrly1 = getCtrlY1();
        double ctrlx2 = getCtrlX2();
        double ctrly2 = getCtrlY2();
        boolean include0 = ((y2 - y1) * (ctrly1 - y1) >= 0);
        boolean include1 = ((y1 - y2) * (ctrly2 - y2) >= 0);
        double[] eqn = new double[4];
        double[] res = new double[4];
        fillEqn(eqn, y, y1, ctrly1, ctrly2, y2);
        int roots = solveCubic(eqn, res);
        roots = evalCubic(res, roots, include0, include1, eqn, x1, ctrlx1, ctrlx2, x2);
        while (--roots >= 0) {
            if (x < res[roots]) {
                crossings++;
            }
        }
        return ((crossings & 1) == 1);
    }
    
    public boolean contains(Point2D p) {
        return contains(p.getX(), p.getY());
    }
    
    private static void fillEqn(double[] eqn, double val, double c1, double cp1, double cp2, double c2) {
        eqn[0] = c1 - val;
        eqn[1] = (cp1 - c1) * 3.0;
        eqn[2] = (cp2 - cp1 - cp1 + c1) * 3.0;
        eqn[3] = c2 + (cp1 - cp2) * 3.0 - c1;
        return;
    }
    
    private static int evalCubic(double[] vals, int num, boolean include0, boolean include1, double[] inflect, double c1, double cp1, double cp2, double c2) {
        int j = 0;
        for (int i = 0; i < num; i++) {
            double t = vals[i];
            if ((include0 ? t >= 0 : t > 0) && (include1 ? t <= 1 : t < 1) && (inflect == null || inflect[1] + (2 * inflect[2] + 3 * inflect[3] * t) * t != 0)) {
                double u = 1 - t;
                vals[j++] = c1 * u * u * u + 3 * cp1 * t * u * u + 3 * cp2 * t * t * u + c2 * t * t * t;
            }
        }
        return j;
    }
    private static final int BELOW = -2;
    private static final int LOWEDGE = -1;
    private static final int INSIDE = 0;
    private static final int HIGHEDGE = 1;
    private static final int ABOVE = 2;
    
    private static int getTag(double coord, double low, double high) {
        if (coord <= low) {
            return (coord < low ? BELOW : LOWEDGE);
        }
        if (coord >= high) {
            return (coord > high ? ABOVE : HIGHEDGE);
        }
        return INSIDE;
    }
    
    private static boolean inwards(int pttag, int opt1tag, int opt2tag) {
        switch (pttag) {
        case BELOW: 
        
        case ABOVE: 
        
        default: 
            return false;
        
        case LOWEDGE: 
            return (opt1tag >= INSIDE || opt2tag >= INSIDE);
        
        case INSIDE: 
            return true;
        
        case HIGHEDGE: 
            return (opt1tag <= INSIDE || opt2tag <= INSIDE);
        
        }
    }
    
    public boolean intersects(double x, double y, double w, double h) {
        if (w < 0 || h < 0) {
            return false;
        }
        double x1 = getX1();
        double y1 = getY1();
        int x1tag = getTag(x1, x, x + w);
        int y1tag = getTag(y1, y, y + h);
        if (x1tag == INSIDE && y1tag == INSIDE) {
            return true;
        }
        double x2 = getX2();
        double y2 = getY2();
        int x2tag = getTag(x2, x, x + w);
        int y2tag = getTag(y2, y, y + h);
        if (x2tag == INSIDE && y2tag == INSIDE) {
            return true;
        }
        double ctrlx1 = getCtrlX1();
        double ctrly1 = getCtrlY1();
        double ctrlx2 = getCtrlX2();
        double ctrly2 = getCtrlY2();
        int ctrlx1tag = getTag(ctrlx1, x, x + w);
        int ctrly1tag = getTag(ctrly1, y, y + h);
        int ctrlx2tag = getTag(ctrlx2, x, x + w);
        int ctrly2tag = getTag(ctrly2, y, y + h);
        if (x1tag < INSIDE && x2tag < INSIDE && ctrlx1tag < INSIDE && ctrlx2tag < INSIDE) {
            return false;
        }
        if (y1tag < INSIDE && y2tag < INSIDE && ctrly1tag < INSIDE && ctrly2tag < INSIDE) {
            return false;
        }
        if (x1tag > INSIDE && x2tag > INSIDE && ctrlx1tag > INSIDE && ctrlx2tag > INSIDE) {
            return false;
        }
        if (y1tag > INSIDE && y2tag > INSIDE && ctrly1tag > INSIDE && ctrly2tag > INSIDE) {
            return false;
        }
        if (inwards(x1tag, x2tag, ctrlx1tag) && inwards(y1tag, y2tag, ctrly1tag)) {
            return true;
        }
        if (inwards(x2tag, x1tag, ctrlx2tag) && inwards(y2tag, y1tag, ctrly2tag)) {
            return true;
        }
        boolean xoverlap = (x1tag * x2tag <= 0);
        boolean yoverlap = (y1tag * y2tag <= 0);
        if (x1tag == INSIDE && x2tag == INSIDE && yoverlap) {
            return true;
        }
        if (y1tag == INSIDE && y2tag == INSIDE && xoverlap) {
            return true;
        }
        double[] eqn = new double[4];
        double[] res = new double[4];
        if (!yoverlap) {
            fillEqn(eqn, (y1tag < INSIDE ? y : y + h), y1, ctrly1, ctrly2, y2);
            int num = solveCubic(eqn, res);
            num = evalCubic(res, num, true, true, null, x1, ctrlx1, ctrlx2, x2);
            return (num == 2 && getTag(res[0], x, x + w) * getTag(res[1], x, x + w) <= 0);
        }
        if (!xoverlap) {
            fillEqn(eqn, (x1tag < INSIDE ? x : x + w), x1, ctrlx1, ctrlx2, x2);
            int num = solveCubic(eqn, res);
            num = evalCubic(res, num, true, true, null, y1, ctrly1, ctrly2, y2);
            return (num == 2 && getTag(res[0], y, y + h) * getTag(res[1], y, y + h) <= 0);
        }
        double dx = x2 - x1;
        double dy = y2 - y1;
        double k = y2 * x1 - x2 * y1;
        int c1tag;
        int c2tag;
        if (y1tag == INSIDE) {
            c1tag = x1tag;
        } else {
            c1tag = getTag((k + dx * (y1tag < INSIDE ? y : y + h)) / dy, x, x + w);
        }
        if (y2tag == INSIDE) {
            c2tag = x2tag;
        } else {
            c2tag = getTag((k + dx * (y2tag < INSIDE ? y : y + h)) / dy, x, x + w);
        }
        if (c1tag * c2tag <= 0) {
            return true;
        }
        c1tag = ((c1tag * x1tag <= 0) ? y1tag : y2tag);
        fillEqn(eqn, (c2tag < INSIDE ? x : x + w), x1, ctrlx1, ctrlx2, x2);
        int num = solveCubic(eqn, res);
        num = evalCubic(res, num, true, true, null, y1, ctrly1, ctrly2, y2);
        int[] tags = new int[num + 1];
        for (int i = 0; i < num; i++) {
            tags[i] = getTag(res[i], y, y + h);
        }
        tags[num] = c1tag;
        Arrays.sort(tags);
        return ((num >= 1 && tags[0] * tags[1] <= 0) || (num >= 3 && tags[2] * tags[3] <= 0));
    }
    
    public boolean intersects(Rectangle2D r) {
        return intersects(r.getX(), r.getY(), r.getWidth(), r.getHeight());
    }
    
    public boolean contains(double x, double y, double w, double h) {
        if (!(contains(x, y) && contains(x + w, y) && contains(x + w, y + h) && contains(x, y + h))) {
            return false;
        }
        Rectangle2D rect = new Rectangle2D$Double(x, y, w, h);
        return !rect.intersectsLine(getX1(), getY1(), getX2(), getY2());
    }
    
    public boolean contains(Rectangle2D r) {
        return contains(r.getX(), r.getY(), r.getWidth(), r.getHeight());
    }
    
    public Rectangle getBounds() {
        return getBounds2D().getBounds();
    }
    
    public PathIterator getPathIterator(AffineTransform at) {
        return new CubicIterator(this, at);
    }
    
    public PathIterator getPathIterator(AffineTransform at, double flatness) {
        return new FlatteningPathIterator(getPathIterator(at), flatness);
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
}
