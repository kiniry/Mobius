package java.awt;

import java.awt.geom.AffineTransform;
import java.awt.geom.PathIterator;
import java.awt.geom.Point2D;
import java.awt.geom.Rectangle2D;
import sun.awt.geom.Crossings;

public class Polygon implements Shape, java.io.Serializable {
    public int npoints;
    public int[] xpoints;
    public int[] ypoints;
    protected Rectangle bounds;
    private static final long serialVersionUID = -6460061437900069969L;
    
    public Polygon() {
        
        xpoints = new int[4];
        ypoints = new int[4];
    }
    
    public Polygon(int[] xpoints, int[] ypoints, int npoints) {
        
        if (npoints > xpoints.length || npoints > ypoints.length) {
            throw new IndexOutOfBoundsException("npoints > xpoints.length || npoints > ypoints.length");
        }
        this.npoints = npoints;
        this.xpoints = new int[npoints];
        this.ypoints = new int[npoints];
        System.arraycopy(xpoints, 0, this.xpoints, 0, npoints);
        System.arraycopy(ypoints, 0, this.ypoints, 0, npoints);
    }
    
    public void reset() {
        npoints = 0;
        bounds = null;
    }
    
    public void invalidate() {
        bounds = null;
    }
    
    public void translate(int deltaX, int deltaY) {
        for (int i = 0; i < npoints; i++) {
            xpoints[i] += deltaX;
            ypoints[i] += deltaY;
        }
        if (bounds != null) {
            bounds.translate(deltaX, deltaY);
        }
    }
    
    void calculateBounds(int[] xpoints, int[] ypoints, int npoints) {
        int boundsMinX = Integer.MAX_VALUE;
        int boundsMinY = Integer.MAX_VALUE;
        int boundsMaxX = Integer.MIN_VALUE;
        int boundsMaxY = Integer.MIN_VALUE;
        for (int i = 0; i < npoints; i++) {
            int x = xpoints[i];
            boundsMinX = Math.min(boundsMinX, x);
            boundsMaxX = Math.max(boundsMaxX, x);
            int y = ypoints[i];
            boundsMinY = Math.min(boundsMinY, y);
            boundsMaxY = Math.max(boundsMaxY, y);
        }
        bounds = new Rectangle(boundsMinX, boundsMinY, boundsMaxX - boundsMinX, boundsMaxY - boundsMinY);
    }
    
    void updateBounds(int x, int y) {
        if (x < bounds.x) {
            bounds.width = bounds.width + (bounds.x - x);
            bounds.x = x;
        } else {
            bounds.width = Math.max(bounds.width, x - bounds.x);
        }
        if (y < bounds.y) {
            bounds.height = bounds.height + (bounds.y - y);
            bounds.y = y;
        } else {
            bounds.height = Math.max(bounds.height, y - bounds.y);
        }
    }
    
    public void addPoint(int x, int y) {
        if (npoints == xpoints.length) {
            int[] tmp;
            tmp = new int[npoints * 2];
            System.arraycopy(xpoints, 0, tmp, 0, npoints);
            xpoints = tmp;
            tmp = new int[npoints * 2];
            System.arraycopy(ypoints, 0, tmp, 0, npoints);
            ypoints = tmp;
        }
        xpoints[npoints] = x;
        ypoints[npoints] = y;
        npoints++;
        if (bounds != null) {
            updateBounds(x, y);
        }
    }
    
    public Rectangle getBounds() {
        return getBoundingBox();
    }
    
    
    public Rectangle getBoundingBox() {
        if (npoints == 0) {
            return new Rectangle();
        }
        if (bounds == null) {
            calculateBounds(xpoints, ypoints, npoints);
        }
        return bounds.getBounds();
    }
    
    public boolean contains(Point p) {
        return contains(p.x, p.y);
    }
    
    public boolean contains(int x, int y) {
        return contains((double)x, (double)y);
    }
    
    
    public boolean inside(int x, int y) {
        return contains((double)x, (double)y);
    }
    
    public Rectangle2D getBounds2D() {
        return getBounds();
    }
    
    public boolean contains(double x, double y) {
        if (npoints <= 2 || !getBoundingBox().contains(x, y)) {
            return false;
        }
        int hits = 0;
        int lastx = xpoints[npoints - 1];
        int lasty = ypoints[npoints - 1];
        int curx;
        int cury;
        for (int i = 0; i < npoints; lastx = curx, lasty = cury, i++) {
            curx = xpoints[i];
            cury = ypoints[i];
            if (cury == lasty) {
                continue;
            }
            int leftx;
            if (curx < lastx) {
                if (x >= lastx) {
                    continue;
                }
                leftx = curx;
            } else {
                if (x >= curx) {
                    continue;
                }
                leftx = lastx;
            }
            double test1;
            double test2;
            if (cury < lasty) {
                if (y < cury || y >= lasty) {
                    continue;
                }
                if (x < leftx) {
                    hits++;
                    continue;
                }
                test1 = x - curx;
                test2 = y - cury;
            } else {
                if (y < lasty || y >= cury) {
                    continue;
                }
                if (x < leftx) {
                    hits++;
                    continue;
                }
                test1 = x - lastx;
                test2 = y - lasty;
            }
            if (test1 < (test2 / (lasty - cury) * (lastx - curx))) {
                hits++;
            }
        }
        return ((hits & 1) != 0);
    }
    
    private Crossings getCrossings(double xlo, double ylo, double xhi, double yhi) {
        Crossings cross = new Crossings$EvenOdd(xlo, ylo, xhi, yhi);
        int lastx = xpoints[npoints - 1];
        int lasty = ypoints[npoints - 1];
        int curx;
        int cury;
        for (int i = 0; i < npoints; i++) {
            curx = xpoints[i];
            cury = ypoints[i];
            if (cross.accumulateLine(lastx, lasty, curx, cury)) {
                return null;
            }
            lastx = curx;
            lasty = cury;
        }
        return cross;
    }
    
    public boolean contains(Point2D p) {
        return contains(p.getX(), p.getY());
    }
    
    public boolean intersects(double x, double y, double w, double h) {
        if (npoints <= 0 || !getBoundingBox().intersects(x, y, w, h)) {
            return false;
        }
        Crossings cross = getCrossings(x, y, x + w, y + h);
        return (cross == null || !cross.isEmpty());
    }
    
    public boolean intersects(Rectangle2D r) {
        return intersects(r.getX(), r.getY(), r.getWidth(), r.getHeight());
    }
    
    public boolean contains(double x, double y, double w, double h) {
        if (npoints <= 0 || !getBoundingBox().intersects(x, y, w, h)) {
            return false;
        }
        Crossings cross = getCrossings(x, y, x + w, y + h);
        return (cross != null && cross.covers(y, y + h));
    }
    
    public boolean contains(Rectangle2D r) {
        return contains(r.getX(), r.getY(), r.getWidth(), r.getHeight());
    }
    
    public PathIterator getPathIterator(AffineTransform at) {
        return new Polygon$PolygonPathIterator(this, this, at);
    }
    
    public PathIterator getPathIterator(AffineTransform at, double flatness) {
        return getPathIterator(at);
    }
    {
    }
}
