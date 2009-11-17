package java.awt;

import java.awt.geom.PathIterator;
import sun.dc.path.PathConsumer;
import sun.dc.path.PathException;
import sun.dc.pr.PathStroker;
import sun.dc.pr.PathDasher;
import sun.dc.pr.Rasterizer;

public class BasicStroke implements Stroke {
    public static final int JOIN_MITER = 0;
    public static final int JOIN_ROUND = 1;
    public static final int JOIN_BEVEL = 2;
    public static final int CAP_BUTT = 0;
    public static final int CAP_ROUND = 1;
    public static final int CAP_SQUARE = 2;
    float width;
    int join;
    int cap;
    float miterlimit;
    float[] dash;
    float dash_phase;
    
    public BasicStroke(float width, int cap, int join, float miterlimit, float[] dash, float dash_phase) {
        
        if (width < 0.0F) {
            throw new IllegalArgumentException("negative width");
        }
        if (cap != CAP_BUTT && cap != CAP_ROUND && cap != CAP_SQUARE) {
            throw new IllegalArgumentException("illegal end cap value");
        }
        if (join == JOIN_MITER) {
            if (miterlimit < 1.0F) {
                throw new IllegalArgumentException("miter limit < 1");
            }
        } else if (join != JOIN_ROUND && join != JOIN_BEVEL) {
            throw new IllegalArgumentException("illegal line join value");
        }
        if (dash != null) {
            if (dash_phase < 0.0F) {
                throw new IllegalArgumentException("negative dash phase");
            }
            boolean allzero = true;
            for (int i = 0; i < dash.length; i++) {
                float d = dash[i];
                if (d > 0.0) {
                    allzero = false;
                } else if (d < 0.0) {
                    throw new IllegalArgumentException("negative dash length");
                }
            }
            if (allzero) {
                throw new IllegalArgumentException("dash lengths all zero");
            }
        }
        this.width = width;
        this.cap = cap;
        this.join = join;
        this.miterlimit = miterlimit;
        if (dash != null) {
            this.dash = (float[])(float[])dash.clone();
        }
        this.dash_phase = dash_phase;
    }
    
    public BasicStroke(float width, int cap, int join, float miterlimit) {
        this(width, cap, join, miterlimit, null, 0.0F);
    }
    
    public BasicStroke(float width, int cap, int join) {
        this(width, cap, join, 10.0F, null, 0.0F);
    }
    
    public BasicStroke(float width) {
        this(width, CAP_SQUARE, JOIN_MITER, 10.0F, null, 0.0F);
    }
    
    public BasicStroke() {
        this(1.0F, CAP_SQUARE, JOIN_MITER, 10.0F, null, 0.0F);
    }
    
    public Shape createStrokedShape(Shape s) {
        BasicStroke$FillAdapter filler = new BasicStroke$FillAdapter(this);
        PathStroker stroker = new PathStroker(filler);
        PathDasher dasher = null;
        try {
            PathConsumer consumer;
            stroker.setPenDiameter(width);
            stroker.setPenT4(null);
            stroker.setCaps(RasterizerCaps[cap]);
            stroker.setCorners(RasterizerCorners[join], miterlimit);
            if (dash != null) {
                dasher = new PathDasher(stroker);
                dasher.setDash(dash, dash_phase);
                dasher.setDashT4(null);
                consumer = dasher;
            } else {
                consumer = stroker;
            }
            feedConsumer(consumer, s.getPathIterator(null));
        } finally {
            stroker.dispose();
            if (dasher != null) {
                dasher.dispose();
            }
        }
        return filler.getShape();
    }
    
    private void feedConsumer(PathConsumer consumer, PathIterator pi) {
        try {
            consumer.beginPath();
            boolean pathClosed = false;
            float mx = 0.0F;
            float my = 0.0F;
            float[] point = new float[6];
            while (!pi.isDone()) {
                int type = pi.currentSegment(point);
                if (pathClosed == true) {
                    pathClosed = false;
                    if (type != PathIterator.SEG_MOVETO) {
                        consumer.beginSubpath(mx, my);
                    }
                }
                switch (type) {
                case PathIterator.SEG_MOVETO: 
                    mx = point[0];
                    my = point[1];
                    consumer.beginSubpath(point[0], point[1]);
                    break;
                
                case PathIterator.SEG_LINETO: 
                    consumer.appendLine(point[0], point[1]);
                    break;
                
                case PathIterator.SEG_QUADTO: 
                    consumer.appendQuadratic(point[0], point[1], point[2], point[3]);
                    break;
                
                case PathIterator.SEG_CUBICTO: 
                    consumer.appendCubic(point[0], point[1], point[2], point[3], point[4], point[5]);
                    break;
                
                case PathIterator.SEG_CLOSE: 
                    consumer.closedSubpath();
                    pathClosed = true;
                    break;
                
                }
                pi.next();
            }
            consumer.endPath();
        } catch (PathException e) {
            throw new InternalError("Unable to Stroke shape (" + e.getMessage() + ")");
        }
    }
    
    public float getLineWidth() {
        return width;
    }
    
    public int getEndCap() {
        return cap;
    }
    
    public int getLineJoin() {
        return join;
    }
    
    public float getMiterLimit() {
        return miterlimit;
    }
    
    public float[] getDashArray() {
        if (dash == null) {
            return null;
        }
        return (float[])(float[])dash.clone();
    }
    
    public float getDashPhase() {
        return dash_phase;
    }
    
    public int hashCode() {
        int hash = Float.floatToIntBits(width);
        hash = hash * 31 + join;
        hash = hash * 31 + cap;
        hash = hash * 31 + Float.floatToIntBits(miterlimit);
        if (dash != null) {
            hash = hash * 31 + Float.floatToIntBits(dash_phase);
            for (int i = 0; i < dash.length; i++) {
                hash = hash * 31 + Float.floatToIntBits(dash[i]);
            }
        }
        return hash;
    }
    
    public boolean equals(Object obj) {
        if (!(obj instanceof BasicStroke)) {
            return false;
        }
        BasicStroke bs = (BasicStroke)(BasicStroke)obj;
        if (width != bs.width) {
            return false;
        }
        if (join != bs.join) {
            return false;
        }
        if (cap != bs.cap) {
            return false;
        }
        if (miterlimit != bs.miterlimit) {
            return false;
        }
        if (dash != null) {
            if (dash_phase != bs.dash_phase) {
                return false;
            }
            if (!java.util.Arrays.equals(dash, bs.dash)) {
                return false;
            }
        } else if (bs.dash != null) {
            return false;
        }
        return true;
    }
    private static final int[] RasterizerCaps = {Rasterizer.BUTT, Rasterizer.ROUND, Rasterizer.SQUARE};
    private static final int[] RasterizerCorners = {Rasterizer.MITER, Rasterizer.ROUND, Rasterizer.BEVEL};
    {
    }
}
