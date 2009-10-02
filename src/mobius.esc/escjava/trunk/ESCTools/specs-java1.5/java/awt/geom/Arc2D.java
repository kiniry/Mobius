package java.awt.geom;

public abstract class Arc2D extends RectangularShape {
    public static final int OPEN = 0;
    public static final int CHORD = 1;
    public static final int PIE = 2;
    {
    }
    {
    }
    private int type;
    
    protected Arc2D(int type) {
        
        setArcType(type);
    }
    
    public abstract double getAngleStart();
    
    public abstract double getAngleExtent();
    
    public int getArcType() {
        return type;
    }
    
    public Point2D getStartPoint() {
        double angle = Math.toRadians(-getAngleStart());
        double x = getX() + (Math.cos(angle) * 0.5 + 0.5) * getWidth();
        double y = getY() + (Math.sin(angle) * 0.5 + 0.5) * getHeight();
        return new Point2D$Double(x, y);
    }
    
    public Point2D getEndPoint() {
        double angle = Math.toRadians(-getAngleStart() - getAngleExtent());
        double x = getX() + (Math.cos(angle) * 0.5 + 0.5) * getWidth();
        double y = getY() + (Math.sin(angle) * 0.5 + 0.5) * getHeight();
        return new Point2D$Double(x, y);
    }
    
    public abstract void setArc(double x, double y, double w, double h, double angSt, double angExt, int closure);
    
    public void setArc(Point2D loc, Dimension2D size, double angSt, double angExt, int closure) {
        setArc(loc.getX(), loc.getY(), size.getWidth(), size.getHeight(), angSt, angExt, closure);
    }
    
    public void setArc(Rectangle2D rect, double angSt, double angExt, int closure) {
        setArc(rect.getX(), rect.getY(), rect.getWidth(), rect.getHeight(), angSt, angExt, closure);
    }
    
    public void setArc(Arc2D a) {
        setArc(a.getX(), a.getY(), a.getWidth(), a.getHeight(), a.getAngleStart(), a.getAngleExtent(), a.type);
    }
    
    public void setArcByCenter(double x, double y, double radius, double angSt, double angExt, int closure) {
        setArc(x - radius, y - radius, radius * 2.0, radius * 2.0, angSt, angExt, closure);
    }
    
    public void setArcByTangent(Point2D p1, Point2D p2, Point2D p3, double radius) {
        double ang1 = Math.atan2(p1.getY() - p2.getY(), p1.getX() - p2.getX());
        double ang2 = Math.atan2(p3.getY() - p2.getY(), p3.getX() - p2.getX());
        double diff = ang2 - ang1;
        if (diff > Math.PI) {
            ang2 -= Math.PI * 2.0;
        } else if (diff < -Math.PI) {
            ang2 += Math.PI * 2.0;
        }
        double bisect = (ang1 + ang2) / 2.0;
        double theta = Math.abs(ang2 - bisect);
        double dist = radius / Math.sin(theta);
        double x = p2.getX() + dist * Math.cos(bisect);
        double y = p2.getY() + dist * Math.sin(bisect);
        if (ang1 < ang2) {
            ang1 -= Math.PI / 2.0;
            ang2 += Math.PI / 2.0;
        } else {
            ang1 += Math.PI / 2.0;
            ang2 -= Math.PI / 2.0;
        }
        ang1 = Math.toDegrees(-ang1);
        ang2 = Math.toDegrees(-ang2);
        diff = ang2 - ang1;
        if (diff < 0) {
            diff += 360;
        } else {
            diff -= 360;
        }
        setArcByCenter(x, y, radius, ang1, diff, type);
    }
    
    public abstract void setAngleStart(double angSt);
    
    public abstract void setAngleExtent(double angExt);
    
    public void setAngleStart(Point2D p) {
        double dx = getHeight() * (p.getX() - getCenterX());
        double dy = getWidth() * (p.getY() - getCenterY());
        setAngleStart(-Math.toDegrees(Math.atan2(dy, dx)));
    }
    
    public void setAngles(double x1, double y1, double x2, double y2) {
        double x = getCenterX();
        double y = getCenterY();
        double w = getWidth();
        double h = getHeight();
        double ang1 = Math.atan2(w * (y - y1), h * (x1 - x));
        double ang2 = Math.atan2(w * (y - y2), h * (x2 - x));
        ang2 -= ang1;
        if (ang2 <= 0.0) {
            ang2 += Math.PI * 2.0;
        }
        setAngleStart(Math.toDegrees(ang1));
        setAngleExtent(Math.toDegrees(ang2));
    }
    
    public void setAngles(Point2D p1, Point2D p2) {
        setAngles(p1.getX(), p1.getY(), p2.getX(), p2.getY());
    }
    
    public void setArcType(int type) {
        if (type < OPEN || type > PIE) {
            throw new IllegalArgumentException("invalid type for Arc: " + type);
        }
        this.type = type;
    }
    
    public void setFrame(double x, double y, double w, double h) {
        setArc(x, y, w, h, getAngleStart(), getAngleExtent(), type);
    }
    
    public Rectangle2D getBounds2D() {
        if (isEmpty()) {
            return makeBounds(getX(), getY(), getWidth(), getHeight());
        }
        double x1;
        double y1;
        double x2;
        double y2;
        if (getArcType() == PIE) {
            x1 = y1 = x2 = y2 = 0.0;
        } else {
            x1 = y1 = 1.0;
            x2 = y2 = -1.0;
        }
        double angle = 0.0;
        for (int i = 0; i < 6; i++) {
            if (i < 4) {
                angle += 90.0;
                if (!containsAngle(angle)) {
                    continue;
                }
            } else if (i == 4) {
                angle = getAngleStart();
            } else {
                angle += getAngleExtent();
            }
            double rads = Math.toRadians(-angle);
            double xe = Math.cos(rads);
            double ye = Math.sin(rads);
            x1 = Math.min(x1, xe);
            y1 = Math.min(y1, ye);
            x2 = Math.max(x2, xe);
            y2 = Math.max(y2, ye);
        }
        double w = getWidth();
        double h = getHeight();
        x2 = (x2 - x1) * 0.5 * w;
        y2 = (y2 - y1) * 0.5 * h;
        x1 = getX() + (x1 * 0.5 + 0.5) * w;
        y1 = getY() + (y1 * 0.5 + 0.5) * h;
        return makeBounds(x1, y1, x2, y2);
    }
    
    protected abstract Rectangle2D makeBounds(double x, double y, double w, double h);
    
    static double normalizeDegrees(double angle) {
        if (angle > 180.0) {
            if (angle <= (180.0 + 360.0)) {
                angle = angle - 360.0;
            } else {
                angle = Math.IEEEremainder(angle, 360.0);
                if (angle == -180.0) {
                    angle = 180.0;
                }
            }
        } else if (angle <= -180.0) {
            if (angle > (-180.0 - 360.0)) {
                angle = angle + 360.0;
            } else {
                angle = Math.IEEEremainder(angle, 360.0);
                if (angle == -180.0) {
                    angle = 180.0;
                }
            }
        }
        return angle;
    }
    
    public boolean containsAngle(double angle) {
        double angExt = getAngleExtent();
        boolean backwards = (angExt < 0.0);
        if (backwards) {
            angExt = -angExt;
        }
        if (angExt >= 360.0) {
            return true;
        }
        angle = normalizeDegrees(angle) - normalizeDegrees(getAngleStart());
        if (backwards) {
            angle = -angle;
        }
        if (angle < 0.0) {
            angle += 360.0;
        }
        return (angle >= 0.0) && (angle < angExt);
    }
    
    public boolean contains(double x, double y) {
        double ellw = getWidth();
        if (ellw <= 0.0) {
            return false;
        }
        double normx = (x - getX()) / ellw - 0.5;
        double ellh = getHeight();
        if (ellh <= 0.0) {
            return false;
        }
        double normy = (y - getY()) / ellh - 0.5;
        double distSq = (normx * normx + normy * normy);
        if (distSq >= 0.25) {
            return false;
        }
        double angExt = Math.abs(getAngleExtent());
        if (angExt >= 360.0) {
            return true;
        }
        boolean inarc = containsAngle(-Math.toDegrees(Math.atan2(normy, normx)));
        if (type == PIE) {
            return inarc;
        }
        if (inarc) {
            if (angExt >= 180.0) {
                return true;
            }
        } else {
            if (angExt <= 180.0) {
                return false;
            }
        }
        double angle = Math.toRadians(-getAngleStart());
        double x1 = Math.cos(angle);
        double y1 = Math.sin(angle);
        angle += Math.toRadians(-getAngleExtent());
        double x2 = Math.cos(angle);
        double y2 = Math.sin(angle);
        boolean inside = (Line2D.relativeCCW(x1, y1, x2, y2, 2 * normx, 2 * normy) * Line2D.relativeCCW(x1, y1, x2, y2, 0, 0) >= 0);
        return inarc ? !inside : inside;
    }
    
    public boolean intersects(double x, double y, double w, double h) {
        double aw = getWidth();
        double ah = getHeight();
        if (w <= 0 || h <= 0 || aw <= 0 || ah <= 0) {
            return false;
        }
        double ext = getAngleExtent();
        if (ext == 0) {
            return false;
        }
        double ax = getX();
        double ay = getY();
        double axw = ax + aw;
        double ayh = ay + ah;
        double xw = x + w;
        double yh = y + h;
        if (x >= axw || y >= ayh || xw <= ax || yh <= ay) {
            return false;
        }
        double axc = getCenterX();
        double ayc = getCenterY();
        Point2D sp = getStartPoint();
        Point2D ep = getEndPoint();
        double sx = sp.getX();
        double sy = sp.getY();
        double ex = ep.getX();
        double ey = ep.getY();
        if (ayc >= y && ayc <= yh) {
            if ((sx < xw && ex < xw && axc < xw && axw > x && containsAngle(0)) || (sx > x && ex > x && axc > x && ax < xw && containsAngle(180))) {
                return true;
            }
        }
        if (axc >= x && axc <= xw) {
            if ((sy > y && ey > y && ayc > y && ay < yh && containsAngle(90)) || (sy < yh && ey < yh && ayc < yh && ayh > y && containsAngle(270))) {
                return true;
            }
        }
        Rectangle2D rect = new Rectangle2D$Double(x, y, w, h);
        if (type == PIE || Math.abs(ext) > 180) {
            if (rect.intersectsLine(axc, ayc, sx, sy) || rect.intersectsLine(axc, ayc, ex, ey)) {
                return true;
            }
        } else {
            if (rect.intersectsLine(sx, sy, ex, ey)) {
                return true;
            }
        }
        if (contains(x, y) || contains(x + w, y) || contains(x, y + h) || contains(x + w, y + h)) {
            return true;
        }
        return false;
    }
    
    public boolean contains(double x, double y, double w, double h) {
        return contains(x, y, w, h, null);
    }
    
    public boolean contains(Rectangle2D r) {
        return contains(r.getX(), r.getY(), r.getWidth(), r.getHeight(), r);
    }
    
    private boolean contains(double x, double y, double w, double h, Rectangle2D origrect) {
        if (!(contains(x, y) && contains(x + w, y) && contains(x, y + h) && contains(x + w, y + h))) {
            return false;
        }
        if (type != PIE || Math.abs(getAngleExtent()) <= 180.0) {
            return true;
        }
        if (origrect == null) {
            origrect = new Rectangle2D$Double(x, y, w, h);
        }
        double halfW = getWidth() / 2.0;
        double halfH = getHeight() / 2.0;
        double xc = getX() + halfW;
        double yc = getY() + halfH;
        double angle = Math.toRadians(-getAngleStart());
        double xe = xc + halfW * Math.cos(angle);
        double ye = yc + halfH * Math.sin(angle);
        if (origrect.intersectsLine(xc, yc, xe, ye)) {
            return false;
        }
        angle += Math.toRadians(-getAngleExtent());
        xe = xc + halfW * Math.cos(angle);
        ye = yc + halfH * Math.sin(angle);
        return !origrect.intersectsLine(xc, yc, xe, ye);
    }
    
    public PathIterator getPathIterator(AffineTransform at) {
        return new ArcIterator(this, at);
    }
}
