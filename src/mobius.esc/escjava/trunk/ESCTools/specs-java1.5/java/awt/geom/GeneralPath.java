package java.awt.geom;

import java.awt.Shape;
import sun.awt.geom.Curve;
import sun.awt.geom.Crossings;

public final class GeneralPath implements Shape, Cloneable {
    public static final int WIND_EVEN_ODD = PathIterator.WIND_EVEN_ODD;
    public static final int WIND_NON_ZERO = PathIterator.WIND_NON_ZERO;
    private static final byte SEG_MOVETO = (byte)PathIterator.SEG_MOVETO;
    private static final byte SEG_LINETO = (byte)PathIterator.SEG_LINETO;
    private static final byte SEG_QUADTO = (byte)PathIterator.SEG_QUADTO;
    private static final byte SEG_CUBICTO = (byte)PathIterator.SEG_CUBICTO;
    private static final byte SEG_CLOSE = (byte)PathIterator.SEG_CLOSE;
    byte[] pointTypes;
    float[] pointCoords;
    int numTypes;
    int numCoords;
    int windingRule;
    static final int INIT_SIZE = 20;
    static final int EXPAND_MAX = 500;
    
    public GeneralPath() {
        this(WIND_NON_ZERO, INIT_SIZE, INIT_SIZE);
    }
    
    public GeneralPath(int rule) {
        this(rule, INIT_SIZE, INIT_SIZE);
    }
    
    public GeneralPath(int rule, int initialCapacity) {
        this(rule, initialCapacity, initialCapacity);
    }
    
    GeneralPath(int rule, int initialTypes, int initialCoords) {
        
        setWindingRule(rule);
        pointTypes = new byte[initialTypes];
        pointCoords = new float[initialCoords * 2];
    }
    
    public GeneralPath(Shape s) {
        this(WIND_NON_ZERO, INIT_SIZE, INIT_SIZE);
        PathIterator pi = s.getPathIterator(null);
        setWindingRule(pi.getWindingRule());
        append(pi, false);
    }
    
    private void needRoom(int newTypes, int newCoords, boolean needMove) {
        if (needMove && numTypes == 0) {
            throw new IllegalPathStateException("missing initial moveto in path definition");
        }
        int size = pointCoords.length;
        if (numCoords + newCoords > size) {
            int grow = size;
            if (grow > EXPAND_MAX * 2) {
                grow = EXPAND_MAX * 2;
            }
            if (grow < newCoords) {
                grow = newCoords;
            }
            float[] arr = new float[size + grow];
            System.arraycopy(pointCoords, 0, arr, 0, numCoords);
            pointCoords = arr;
        }
        size = pointTypes.length;
        if (numTypes + newTypes > size) {
            int grow = size;
            if (grow > EXPAND_MAX) {
                grow = EXPAND_MAX;
            }
            if (grow < newTypes) {
                grow = newTypes;
            }
            byte[] arr = new byte[size + grow];
            System.arraycopy(pointTypes, 0, arr, 0, numTypes);
            pointTypes = arr;
        }
    }
    
    public synchronized void moveTo(float x, float y) {
        if (numTypes > 0 && pointTypes[numTypes - 1] == SEG_MOVETO) {
            pointCoords[numCoords - 2] = x;
            pointCoords[numCoords - 1] = y;
        } else {
            needRoom(1, 2, false);
            pointTypes[numTypes++] = SEG_MOVETO;
            pointCoords[numCoords++] = x;
            pointCoords[numCoords++] = y;
        }
    }
    
    public synchronized void lineTo(float x, float y) {
        needRoom(1, 2, true);
        pointTypes[numTypes++] = SEG_LINETO;
        pointCoords[numCoords++] = x;
        pointCoords[numCoords++] = y;
    }
    
    public synchronized void quadTo(float x1, float y1, float x2, float y2) {
        needRoom(1, 4, true);
        pointTypes[numTypes++] = SEG_QUADTO;
        pointCoords[numCoords++] = x1;
        pointCoords[numCoords++] = y1;
        pointCoords[numCoords++] = x2;
        pointCoords[numCoords++] = y2;
    }
    
    public synchronized void curveTo(float x1, float y1, float x2, float y2, float x3, float y3) {
        needRoom(1, 6, true);
        pointTypes[numTypes++] = SEG_CUBICTO;
        pointCoords[numCoords++] = x1;
        pointCoords[numCoords++] = y1;
        pointCoords[numCoords++] = x2;
        pointCoords[numCoords++] = y2;
        pointCoords[numCoords++] = x3;
        pointCoords[numCoords++] = y3;
    }
    
    public synchronized void closePath() {
        if (numTypes == 0 || pointTypes[numTypes - 1] != SEG_CLOSE) {
            needRoom(1, 0, true);
            pointTypes[numTypes++] = SEG_CLOSE;
        }
    }
    
    public void append(Shape s, boolean connect) {
        PathIterator pi = s.getPathIterator(null);
        append(pi, connect);
    }
    
    public void append(PathIterator pi, boolean connect) {
        float[] coords = new float[6];
        while (!pi.isDone()) {
            switch (pi.currentSegment(coords)) {
            case SEG_MOVETO: 
                if (!connect || numTypes < 1 || numCoords < 2) {
                    moveTo(coords[0], coords[1]);
                    break;
                }
                if (pointTypes[numTypes - 1] != SEG_CLOSE && pointCoords[numCoords - 2] == coords[0] && pointCoords[numCoords - 1] == coords[1]) {
                    break;
                }
            
            case SEG_LINETO: 
                lineTo(coords[0], coords[1]);
                break;
            
            case SEG_QUADTO: 
                quadTo(coords[0], coords[1], coords[2], coords[3]);
                break;
            
            case SEG_CUBICTO: 
                curveTo(coords[0], coords[1], coords[2], coords[3], coords[4], coords[5]);
                break;
            
            case SEG_CLOSE: 
                closePath();
                break;
            
            }
            pi.next();
            connect = false;
        }
    }
    
    public synchronized int getWindingRule() {
        return windingRule;
    }
    
    public void setWindingRule(int rule) {
        if (rule != WIND_EVEN_ODD && rule != WIND_NON_ZERO) {
            throw new IllegalArgumentException("winding rule must be WIND_EVEN_ODD or WIND_NON_ZERO");
        }
        windingRule = rule;
    }
    
    public synchronized Point2D getCurrentPoint() {
        if (numTypes < 1 || numCoords < 2) {
            return null;
        }
        int index = numCoords;
        if (pointTypes[numTypes - 1] == SEG_CLOSE) {
            loop: for (int i = numTypes - 2; i > 0; i--) {
                switch (pointTypes[i]) {
                case SEG_MOVETO: 
                    break loop;
                
                case SEG_LINETO: 
                    index -= 2;
                    break;
                
                case SEG_QUADTO: 
                    index -= 4;
                    break;
                
                case SEG_CUBICTO: 
                    index -= 6;
                    break;
                
                case SEG_CLOSE: 
                    break;
                
                }
            }
        }
        return new Point2D$Float(pointCoords[index - 2], pointCoords[index - 1]);
    }
    
    public synchronized void reset() {
        numTypes = numCoords = 0;
    }
    
    public void transform(AffineTransform at) {
        at.transform(pointCoords, 0, pointCoords, 0, numCoords / 2);
    }
    
    public synchronized Shape createTransformedShape(AffineTransform at) {
        GeneralPath gp = (GeneralPath)(GeneralPath)clone();
        if (at != null) {
            gp.transform(at);
        }
        return gp;
    }
    
    public java.awt.Rectangle getBounds() {
        return getBounds2D().getBounds();
    }
    
    public synchronized Rectangle2D getBounds2D() {
        float x1;
        float y1;
        float x2;
        float y2;
        int i = numCoords;
        if (i > 0) {
            y1 = y2 = pointCoords[--i];
            x1 = x2 = pointCoords[--i];
            while (i > 0) {
                float y = pointCoords[--i];
                float x = pointCoords[--i];
                if (x < x1) x1 = x;
                if (y < y1) y1 = y;
                if (x > x2) x2 = x;
                if (y > y2) y2 = y;
            }
        } else {
            x1 = y1 = x2 = y2 = 0.0F;
        }
        return new Rectangle2D$Float(x1, y1, x2 - x1, y2 - y1);
    }
    
    public boolean contains(double x, double y) {
        if (numTypes < 2) {
            return false;
        }
        int cross = Curve.crossingsForPath(getPathIterator(null), x, y);
        if (windingRule == WIND_NON_ZERO) {
            return (cross != 0);
        } else {
            return ((cross & 1) != 0);
        }
    }
    
    public boolean contains(Point2D p) {
        return contains(p.getX(), p.getY());
    }
    
    public boolean contains(double x, double y, double w, double h) {
        Crossings c = Crossings.findCrossings(getPathIterator(null), x, y, x + w, y + h);
        return (c != null && c.covers(y, y + h));
    }
    
    public boolean contains(Rectangle2D r) {
        return contains(r.getX(), r.getY(), r.getWidth(), r.getHeight());
    }
    
    public boolean intersects(double x, double y, double w, double h) {
        Crossings c = Crossings.findCrossings(getPathIterator(null), x, y, x + w, y + h);
        return (c == null || !c.isEmpty());
    }
    
    public boolean intersects(Rectangle2D r) {
        return intersects(r.getX(), r.getY(), r.getWidth(), r.getHeight());
    }
    
    public PathIterator getPathIterator(AffineTransform at) {
        return new GeneralPathIterator(this, at);
    }
    
    public PathIterator getPathIterator(AffineTransform at, double flatness) {
        return new FlatteningPathIterator(getPathIterator(at), flatness);
    }
    
    public Object clone() {
        try {
            GeneralPath copy = (GeneralPath)(GeneralPath)super.clone();
            copy.pointTypes = (byte[])(byte[])pointTypes.clone();
            copy.pointCoords = (float[])(float[])pointCoords.clone();
            return copy;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    GeneralPath(int windingRule, byte[] pointTypes, int numTypes, float[] pointCoords, int numCoords) {
        
        this.windingRule = windingRule;
        this.pointTypes = pointTypes;
        this.numTypes = numTypes;
        this.pointCoords = pointCoords;
        this.numCoords = numCoords;
    }
}
