package java.awt.geom;

import java.awt.Shape;

public class AffineTransform implements Cloneable, java.io.Serializable {
    private static final int TYPE_UNKNOWN = -1;
    public static final int TYPE_IDENTITY = 0;
    public static final int TYPE_TRANSLATION = 1;
    public static final int TYPE_UNIFORM_SCALE = 2;
    public static final int TYPE_GENERAL_SCALE = 4;
    public static final int TYPE_MASK_SCALE = (TYPE_UNIFORM_SCALE | TYPE_GENERAL_SCALE);
    public static final int TYPE_FLIP = 64;
    public static final int TYPE_QUADRANT_ROTATION = 8;
    public static final int TYPE_GENERAL_ROTATION = 16;
    public static final int TYPE_MASK_ROTATION = (TYPE_QUADRANT_ROTATION | TYPE_GENERAL_ROTATION);
    public static final int TYPE_GENERAL_TRANSFORM = 32;
    static final int APPLY_IDENTITY = 0;
    static final int APPLY_TRANSLATE = 1;
    static final int APPLY_SCALE = 2;
    static final int APPLY_SHEAR = 4;
    private static final int HI_SHIFT = 3;
    private static final int HI_IDENTITY = APPLY_IDENTITY << HI_SHIFT;
    private static final int HI_TRANSLATE = APPLY_TRANSLATE << HI_SHIFT;
    private static final int HI_SCALE = APPLY_SCALE << HI_SHIFT;
    private static final int HI_SHEAR = APPLY_SHEAR << HI_SHIFT;
    double m00;
    double m10;
    double m01;
    double m11;
    double m02;
    double m12;
    transient int state;
    private transient int type;
    
    private AffineTransform(double m00, double m10, double m01, double m11, double m02, double m12, int state) {
        
        this.m00 = m00;
        this.m10 = m10;
        this.m01 = m01;
        this.m11 = m11;
        this.m02 = m02;
        this.m12 = m12;
        this.state = state;
        this.type = TYPE_UNKNOWN;
    }
    
    public AffineTransform() {
        
        m00 = m11 = 1.0;
    }
    
    public AffineTransform(AffineTransform Tx) {
        
        this.m00 = Tx.m00;
        this.m10 = Tx.m10;
        this.m01 = Tx.m01;
        this.m11 = Tx.m11;
        this.m02 = Tx.m02;
        this.m12 = Tx.m12;
        this.state = Tx.state;
        this.type = Tx.type;
    }
    
    public AffineTransform(float m00, float m10, float m01, float m11, float m02, float m12) {
        
        this.m00 = m00;
        this.m10 = m10;
        this.m01 = m01;
        this.m11 = m11;
        this.m02 = m02;
        this.m12 = m12;
        updateState();
    }
    
    public AffineTransform(float[] flatmatrix) {
        
        m00 = flatmatrix[0];
        m10 = flatmatrix[1];
        m01 = flatmatrix[2];
        m11 = flatmatrix[3];
        if (flatmatrix.length > 5) {
            m02 = flatmatrix[4];
            m12 = flatmatrix[5];
        }
        updateState();
    }
    
    public AffineTransform(double m00, double m10, double m01, double m11, double m02, double m12) {
        
        this.m00 = m00;
        this.m10 = m10;
        this.m01 = m01;
        this.m11 = m11;
        this.m02 = m02;
        this.m12 = m12;
        updateState();
    }
    
    public AffineTransform(double[] flatmatrix) {
        
        m00 = flatmatrix[0];
        m10 = flatmatrix[1];
        m01 = flatmatrix[2];
        m11 = flatmatrix[3];
        if (flatmatrix.length > 5) {
            m02 = flatmatrix[4];
            m12 = flatmatrix[5];
        }
        updateState();
    }
    
    public static AffineTransform getTranslateInstance(double tx, double ty) {
        AffineTransform Tx = new AffineTransform();
        Tx.setToTranslation(tx, ty);
        return Tx;
    }
    
    public static AffineTransform getRotateInstance(double theta) {
        AffineTransform Tx = new AffineTransform();
        Tx.setToRotation(theta);
        return Tx;
    }
    
    public static AffineTransform getRotateInstance(double theta, double x, double y) {
        AffineTransform Tx = new AffineTransform();
        Tx.setToRotation(theta, x, y);
        return Tx;
    }
    
    public static AffineTransform getScaleInstance(double sx, double sy) {
        AffineTransform Tx = new AffineTransform();
        Tx.setToScale(sx, sy);
        return Tx;
    }
    
    public static AffineTransform getShearInstance(double shx, double shy) {
        AffineTransform Tx = new AffineTransform();
        Tx.setToShear(shx, shy);
        return Tx;
    }
    
    public int getType() {
        if (type == TYPE_UNKNOWN) {
            calculateType();
        }
        return type;
    }
    
    private void calculateType() {
        int ret = TYPE_IDENTITY;
        boolean sgn0;
        boolean sgn1;
        double M0;
        double M1;
        double M2;
        double M3;
        updateState();
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            ret = TYPE_TRANSLATION;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            if ((M0 = m00) * (M2 = m01) + (M3 = m10) * (M1 = m11) != 0) {
                this.type = TYPE_GENERAL_TRANSFORM;
                return;
            }
            sgn0 = (M0 >= 0.0);
            sgn1 = (M1 >= 0.0);
            if (sgn0 == sgn1) {
                if (M0 != M1 || M2 != -M3) {
                    ret |= (TYPE_GENERAL_ROTATION | TYPE_GENERAL_SCALE);
                } else if (M0 * M1 - M2 * M3 != 1.0) {
                    ret |= (TYPE_GENERAL_ROTATION | TYPE_UNIFORM_SCALE);
                } else {
                    ret |= TYPE_GENERAL_ROTATION;
                }
            } else {
                if (M0 != -M1 || M2 != M3) {
                    ret |= (TYPE_GENERAL_ROTATION | TYPE_FLIP | TYPE_GENERAL_SCALE);
                } else if (M0 * M1 - M2 * M3 != 1.0) {
                    ret |= (TYPE_GENERAL_ROTATION | TYPE_FLIP | TYPE_UNIFORM_SCALE);
                } else {
                    ret |= (TYPE_GENERAL_ROTATION | TYPE_FLIP);
                }
            }
            break;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            ret = TYPE_TRANSLATION;
        
        case (APPLY_SHEAR): 
            sgn0 = ((M0 = m01) >= 0.0);
            sgn1 = ((M1 = m10) >= 0.0);
            if (sgn0 != sgn1) {
                if (M0 != -M1) {
                    ret |= (TYPE_QUADRANT_ROTATION | TYPE_GENERAL_SCALE);
                } else if (M0 != 1.0 && M0 != -1.0) {
                    ret |= (TYPE_QUADRANT_ROTATION | TYPE_UNIFORM_SCALE);
                } else {
                    ret |= TYPE_QUADRANT_ROTATION;
                }
            } else {
                if (M0 == M1) {
                    ret |= (TYPE_QUADRANT_ROTATION | TYPE_FLIP | TYPE_UNIFORM_SCALE);
                } else {
                    ret |= (TYPE_QUADRANT_ROTATION | TYPE_FLIP | TYPE_GENERAL_SCALE);
                }
            }
            break;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            ret = TYPE_TRANSLATION;
        
        case (APPLY_SCALE): 
            sgn0 = ((M0 = m00) >= 0.0);
            sgn1 = ((M1 = m11) >= 0.0);
            if (sgn0 == sgn1) {
                if (sgn0) {
                    if (M0 == M1) {
                        ret |= TYPE_UNIFORM_SCALE;
                    } else {
                        ret |= TYPE_GENERAL_SCALE;
                    }
                } else {
                    if (M0 != M1) {
                        ret |= (TYPE_QUADRANT_ROTATION | TYPE_GENERAL_SCALE);
                    } else if (M0 != -1.0) {
                        ret |= (TYPE_QUADRANT_ROTATION | TYPE_UNIFORM_SCALE);
                    } else {
                        ret |= TYPE_QUADRANT_ROTATION;
                    }
                }
            } else {
                if (M0 == -M1) {
                    if (M0 == 1.0 || M0 == -1.0) {
                        ret |= TYPE_FLIP;
                    } else {
                        ret |= (TYPE_FLIP | TYPE_UNIFORM_SCALE);
                    }
                } else {
                    ret |= (TYPE_FLIP | TYPE_GENERAL_SCALE);
                }
            }
            break;
        
        case (APPLY_TRANSLATE): 
            ret = TYPE_TRANSLATION;
            break;
        
        case (APPLY_IDENTITY): 
            break;
        
        }
        this.type = ret;
    }
    
    public double getDeterminant() {
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            return m00 * m11 - m01 * m10;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR): 
            return -(m01 * m10);
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SCALE): 
            return m00 * m11;
        
        case (APPLY_TRANSLATE): 
        
        case (APPLY_IDENTITY): 
            return 1.0;
        
        }
    }
    
    void updateState() {
        if (m01 == 0.0 && m10 == 0.0) {
            if (m00 == 1.0 && m11 == 1.0) {
                if (m02 == 0.0 && m12 == 0.0) {
                    state = APPLY_IDENTITY;
                    type = TYPE_IDENTITY;
                } else {
                    state = APPLY_TRANSLATE;
                    type = TYPE_TRANSLATION;
                }
            } else {
                if (m02 == 0.0 && m12 == 0.0) {
                    state = APPLY_SCALE;
                    type = TYPE_UNKNOWN;
                } else {
                    state = (APPLY_SCALE | APPLY_TRANSLATE);
                    type = TYPE_UNKNOWN;
                }
            }
        } else {
            if (m00 == 0.0 && m11 == 0.0) {
                if (m02 == 0.0 && m12 == 0.0) {
                    state = APPLY_SHEAR;
                    type = TYPE_UNKNOWN;
                } else {
                    state = (APPLY_SHEAR | APPLY_TRANSLATE);
                    type = TYPE_UNKNOWN;
                }
            } else {
                if (m02 == 0.0 && m12 == 0.0) {
                    state = (APPLY_SHEAR | APPLY_SCALE);
                    type = TYPE_UNKNOWN;
                } else {
                    state = (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE);
                    type = TYPE_UNKNOWN;
                }
            }
        }
    }
    
    private void stateError() {
        throw new InternalError("missing case in transform state switch");
    }
    
    public void getMatrix(double[] flatmatrix) {
        flatmatrix[0] = m00;
        flatmatrix[1] = m10;
        flatmatrix[2] = m01;
        flatmatrix[3] = m11;
        if (flatmatrix.length > 5) {
            flatmatrix[4] = m02;
            flatmatrix[5] = m12;
        }
    }
    
    public double getScaleX() {
        return m00;
    }
    
    public double getScaleY() {
        return m11;
    }
    
    public double getShearX() {
        return m01;
    }
    
    public double getShearY() {
        return m10;
    }
    
    public double getTranslateX() {
        return m02;
    }
    
    public double getTranslateY() {
        return m12;
    }
    
    public void translate(double tx, double ty) {
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            m02 = tx * m00 + ty * m01 + m02;
            m12 = tx * m10 + ty * m11 + m12;
            if (m02 == 0.0 && m12 == 0.0) {
                state = APPLY_SHEAR | APPLY_SCALE;
                if (type != TYPE_UNKNOWN) {
                    type -= TYPE_TRANSLATION;
                }
            }
            return;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            m02 = tx * m00 + ty * m01;
            m12 = tx * m10 + ty * m11;
            if (m02 != 0.0 || m12 != 0.0) {
                state = APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE;
                type |= TYPE_TRANSLATION;
            }
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            m02 = ty * m01 + m02;
            m12 = tx * m10 + m12;
            if (m02 == 0.0 && m12 == 0.0) {
                state = APPLY_SHEAR;
                if (type != TYPE_UNKNOWN) {
                    type -= TYPE_TRANSLATION;
                }
            }
            return;
        
        case (APPLY_SHEAR): 
            m02 = ty * m01;
            m12 = tx * m10;
            if (m02 != 0.0 || m12 != 0.0) {
                state = APPLY_SHEAR | APPLY_TRANSLATE;
                type |= TYPE_TRANSLATION;
            }
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            m02 = tx * m00 + m02;
            m12 = ty * m11 + m12;
            if (m02 == 0.0 && m12 == 0.0) {
                state = APPLY_SCALE;
                if (type != TYPE_UNKNOWN) {
                    type -= TYPE_TRANSLATION;
                }
            }
            return;
        
        case (APPLY_SCALE): 
            m02 = tx * m00;
            m12 = ty * m11;
            if (m02 != 0.0 || m12 != 0.0) {
                state = APPLY_SCALE | APPLY_TRANSLATE;
                type |= TYPE_TRANSLATION;
            }
            return;
        
        case (APPLY_TRANSLATE): 
            m02 = tx + m02;
            m12 = ty + m12;
            if (m02 == 0.0 && m12 == 0.0) {
                state = APPLY_IDENTITY;
                type = TYPE_IDENTITY;
            }
            return;
        
        case (APPLY_IDENTITY): 
            m02 = tx;
            m12 = ty;
            if (tx != 0.0 || ty != 0.0) {
                state = APPLY_TRANSLATE;
                type = TYPE_TRANSLATION;
            }
            return;
        
        }
    }
    
    public void rotate(double theta) {
        double sin = Math.sin(theta);
        double cos = Math.cos(theta);
        if (Math.abs(sin) < 1.0E-15) {
            if (cos < 0.0) {
                m00 = -m00;
                m11 = -m11;
                int state = this.state;
                if ((state & (APPLY_SHEAR)) != 0) {
                    m01 = -m01;
                    m10 = -m10;
                } else {
                    if (m00 == 1.0 && m11 == 1.0) {
                        this.state = state & ~APPLY_SCALE;
                    } else {
                        this.state = state | APPLY_SCALE;
                    }
                }
                type = TYPE_UNKNOWN;
            }
            return;
        }
        if (Math.abs(cos) < 1.0E-15) {
            if (sin < 0.0) {
                double M0 = m00;
                m00 = -m01;
                m01 = M0;
                M0 = m10;
                m10 = -m11;
                m11 = M0;
            } else {
                double M0 = m00;
                m00 = m01;
                m01 = -M0;
                M0 = m10;
                m10 = m11;
                m11 = -M0;
            }
            int state = rot90conversion[this.state];
            if ((state & (APPLY_SHEAR | APPLY_SCALE)) == APPLY_SCALE && m00 == 1.0 && m11 == 1.0) {
                state -= APPLY_SCALE;
            }
            this.state = state;
            type = TYPE_UNKNOWN;
            return;
        }
        double M0;
        double M1;
        M0 = m00;
        M1 = m01;
        m00 = cos * M0 + sin * M1;
        m01 = -sin * M0 + cos * M1;
        M0 = m10;
        M1 = m11;
        m10 = cos * M0 + sin * M1;
        m11 = -sin * M0 + cos * M1;
        updateState();
    }
    private static int[] rot90conversion = {APPLY_SHEAR, APPLY_SHEAR | APPLY_TRANSLATE, APPLY_SHEAR, APPLY_SHEAR | APPLY_TRANSLATE, APPLY_SCALE, APPLY_SCALE | APPLY_TRANSLATE, APPLY_SHEAR | APPLY_SCALE, APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE};
    
    public void rotate(double theta, double x, double y) {
        translate(x, y);
        rotate(theta);
        translate(-x, -y);
    }
    
    public void scale(double sx, double sy) {
        int state = this.state;
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            m00 *= sx;
            m11 *= sy;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR): 
            m01 *= sy;
            m10 *= sx;
            if (m01 == 0 && m10 == 0) {
                this.state = state - APPLY_SHEAR;
            }
            this.type = TYPE_UNKNOWN;
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SCALE): 
            m00 *= sx;
            m11 *= sy;
            if (m00 == 1.0 && m11 == 1.0) {
                this.state = (state &= APPLY_TRANSLATE);
                this.type = (state == APPLY_IDENTITY ? TYPE_IDENTITY : TYPE_TRANSLATION);
            } else {
                this.type = TYPE_UNKNOWN;
            }
            return;
        
        case (APPLY_TRANSLATE): 
        
        case (APPLY_IDENTITY): 
            m00 = sx;
            m11 = sy;
            if (sx != 1.0 || sy != 1.0) {
                this.state = state | APPLY_SCALE;
                this.type = TYPE_UNKNOWN;
            }
            return;
        
        }
    }
    
    public void shear(double shx, double shy) {
        int state = this.state;
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            double M0;
            double M1;
            M0 = m00;
            M1 = m01;
            m00 = M0 + M1 * shy;
            m01 = M0 * shx + M1;
            M0 = m10;
            M1 = m11;
            m10 = M0 + M1 * shy;
            m11 = M0 * shx + M1;
            updateState();
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR): 
            m00 = m01 * shy;
            m11 = m10 * shx;
            if (m00 != 0.0 || m11 != 0.0) {
                this.state = state | APPLY_SCALE;
            }
            this.type = TYPE_UNKNOWN;
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SCALE): 
            m01 = m00 * shx;
            m10 = m11 * shy;
            if (m01 != 0.0 || m10 != 0.0) {
                this.state = state | APPLY_SHEAR;
            }
            this.type = TYPE_UNKNOWN;
            return;
        
        case (APPLY_TRANSLATE): 
        
        case (APPLY_IDENTITY): 
            m01 = shx;
            m10 = shy;
            if (m01 != 0.0 || m10 != 0.0) {
                this.state = state | APPLY_SCALE | APPLY_SHEAR;
                this.type = TYPE_UNKNOWN;
            }
            return;
        
        }
    }
    
    public void setToIdentity() {
        m00 = m11 = 1.0;
        m10 = m01 = m02 = m12 = 0.0;
        state = APPLY_IDENTITY;
        type = TYPE_IDENTITY;
    }
    
    public void setToTranslation(double tx, double ty) {
        m00 = 1.0;
        m10 = 0.0;
        m01 = 0.0;
        m11 = 1.0;
        m02 = tx;
        m12 = ty;
        if (tx != 0.0 || ty != 0.0) {
            state = APPLY_TRANSLATE;
            type = TYPE_TRANSLATION;
        } else {
            state = APPLY_IDENTITY;
            type = TYPE_IDENTITY;
        }
    }
    
    public void setToRotation(double theta) {
        m02 = 0.0;
        m12 = 0.0;
        double sin = Math.sin(theta);
        double cos = Math.cos(theta);
        if (Math.abs(sin) < 1.0E-15) {
            m01 = m10 = 0.0;
            if (cos < 0) {
                m00 = m11 = -1.0;
                state = APPLY_SCALE;
                type = TYPE_QUADRANT_ROTATION;
            } else {
                m00 = m11 = 1.0;
                state = APPLY_IDENTITY;
                type = TYPE_IDENTITY;
            }
            return;
        }
        if (Math.abs(cos) < 1.0E-15) {
            m00 = m11 = 0.0;
            if (sin < 0.0) {
                m01 = 1.0;
                m10 = -1.0;
            } else {
                m01 = -1.0;
                m10 = 1.0;
            }
            state = APPLY_SHEAR;
            type = TYPE_QUADRANT_ROTATION;
            return;
        }
        m00 = cos;
        m01 = -sin;
        m10 = sin;
        m11 = cos;
        state = APPLY_SHEAR | APPLY_SCALE;
        type = TYPE_GENERAL_ROTATION;
        return;
    }
    
    public void setToRotation(double theta, double x, double y) {
        setToRotation(theta);
        double sin = m10;
        double oneMinusCos = 1.0 - m00;
        m02 = x * oneMinusCos + y * sin;
        m12 = y * oneMinusCos - x * sin;
        if (m02 != 0.0 || m12 != 0.0) {
            state |= APPLY_TRANSLATE;
            type |= TYPE_TRANSLATION;
        }
        return;
    }
    
    public void setToScale(double sx, double sy) {
        m00 = sx;
        m10 = 0.0;
        m01 = 0.0;
        m11 = sy;
        m02 = 0.0;
        m12 = 0.0;
        if (sx != 1.0 || sy != 1.0) {
            state = APPLY_SCALE;
            type = TYPE_UNKNOWN;
        } else {
            state = APPLY_IDENTITY;
            type = TYPE_IDENTITY;
        }
    }
    
    public void setToShear(double shx, double shy) {
        m00 = 1.0;
        m01 = shx;
        m10 = shy;
        m11 = 1.0;
        m02 = 0.0;
        m12 = 0.0;
        if (shx != 0.0 || shy != 0.0) {
            state = (APPLY_SHEAR | APPLY_SCALE);
            type = TYPE_UNKNOWN;
        } else {
            state = APPLY_IDENTITY;
            type = TYPE_IDENTITY;
        }
    }
    
    public void setTransform(AffineTransform Tx) {
        this.m00 = Tx.m00;
        this.m10 = Tx.m10;
        this.m01 = Tx.m01;
        this.m11 = Tx.m11;
        this.m02 = Tx.m02;
        this.m12 = Tx.m12;
        this.state = Tx.state;
        this.type = Tx.type;
    }
    
    public void setTransform(double m00, double m10, double m01, double m11, double m02, double m12) {
        this.m00 = m00;
        this.m10 = m10;
        this.m01 = m01;
        this.m11 = m11;
        this.m02 = m02;
        this.m12 = m12;
        updateState();
    }
    
    public void concatenate(AffineTransform Tx) {
        double M0;
        double M1;
        double T00;
        double T01;
        double T10;
        double T11;
        double T02;
        double T12;
        int mystate = state;
        int txstate = Tx.state;
        switch ((txstate << HI_SHIFT) | mystate) {
        case (HI_IDENTITY | APPLY_IDENTITY): 
        
        case (HI_IDENTITY | APPLY_TRANSLATE): 
        
        case (HI_IDENTITY | APPLY_SCALE): 
        
        case (HI_IDENTITY | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_IDENTITY | APPLY_SHEAR): 
        
        case (HI_IDENTITY | APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_IDENTITY | APPLY_SHEAR | APPLY_SCALE): 
        
        case (HI_IDENTITY | APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            return;
        
        case (HI_SHEAR | HI_SCALE | HI_TRANSLATE | APPLY_IDENTITY): 
            m01 = Tx.m01;
            m10 = Tx.m10;
        
        case (HI_SCALE | HI_TRANSLATE | APPLY_IDENTITY): 
            m00 = Tx.m00;
            m11 = Tx.m11;
        
        case (HI_TRANSLATE | APPLY_IDENTITY): 
            m02 = Tx.m02;
            m12 = Tx.m12;
            state = txstate;
            type = Tx.type;
            return;
        
        case (HI_SHEAR | HI_SCALE | APPLY_IDENTITY): 
            m01 = Tx.m01;
            m10 = Tx.m10;
        
        case (HI_SCALE | APPLY_IDENTITY): 
            m00 = Tx.m00;
            m11 = Tx.m11;
            state = txstate;
            type = Tx.type;
            return;
        
        case (HI_SHEAR | HI_TRANSLATE | APPLY_IDENTITY): 
            m02 = Tx.m02;
            m12 = Tx.m12;
        
        case (HI_SHEAR | APPLY_IDENTITY): 
            m01 = Tx.m01;
            m10 = Tx.m10;
            m00 = m11 = 0.0;
            state = txstate;
            type = Tx.type;
            return;
        
        case (HI_TRANSLATE | APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_TRANSLATE | APPLY_SHEAR | APPLY_SCALE): 
        
        case (HI_TRANSLATE | APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_TRANSLATE | APPLY_SHEAR): 
        
        case (HI_TRANSLATE | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_TRANSLATE | APPLY_SCALE): 
        
        case (HI_TRANSLATE | APPLY_TRANSLATE): 
            translate(Tx.m02, Tx.m12);
            return;
        
        case (HI_SCALE | APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SCALE | APPLY_SHEAR | APPLY_SCALE): 
        
        case (HI_SCALE | APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_SCALE | APPLY_SHEAR): 
        
        case (HI_SCALE | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SCALE | APPLY_SCALE): 
        
        case (HI_SCALE | APPLY_TRANSLATE): 
            scale(Tx.m00, Tx.m11);
            return;
        
        case (HI_SHEAR | APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SHEAR | APPLY_SHEAR | APPLY_SCALE): 
            T01 = Tx.m01;
            T10 = Tx.m10;
            M0 = m00;
            m00 = m01 * T10;
            m01 = M0 * T01;
            M0 = m10;
            m10 = m11 * T10;
            m11 = M0 * T01;
            type = TYPE_UNKNOWN;
            return;
        
        case (HI_SHEAR | APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_SHEAR | APPLY_SHEAR): 
            m00 = m01 * Tx.m10;
            m01 = 0.0;
            m11 = m10 * Tx.m01;
            m10 = 0.0;
            state = mystate ^ (APPLY_SHEAR | APPLY_SCALE);
            type = TYPE_UNKNOWN;
            return;
        
        case (HI_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SHEAR | APPLY_SCALE): 
            m01 = m00 * Tx.m01;
            m00 = 0.0;
            m10 = m11 * Tx.m10;
            m11 = 0.0;
            state = mystate ^ (APPLY_SHEAR | APPLY_SCALE);
            type = TYPE_UNKNOWN;
            return;
        
        case (HI_SHEAR | APPLY_TRANSLATE): 
            m00 = 0.0;
            m01 = Tx.m01;
            m10 = Tx.m10;
            m11 = 0.0;
            state = APPLY_TRANSLATE | APPLY_SHEAR;
            type = TYPE_UNKNOWN;
            return;
        
        }
        T00 = Tx.m00;
        T01 = Tx.m01;
        T02 = Tx.m02;
        T10 = Tx.m10;
        T11 = Tx.m11;
        T12 = Tx.m12;
        switch (mystate) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            state = mystate | txstate;
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            M0 = m00;
            M1 = m01;
            m00 = T00 * M0 + T10 * M1;
            m01 = T01 * M0 + T11 * M1;
            m02 += T02 * M0 + T12 * M1;
            M0 = m10;
            M1 = m11;
            m10 = T00 * M0 + T10 * M1;
            m11 = T01 * M0 + T11 * M1;
            m12 += T02 * M0 + T12 * M1;
            type = TYPE_UNKNOWN;
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR): 
            M0 = m01;
            m00 = T10 * M0;
            m01 = T11 * M0;
            m02 += T12 * M0;
            M0 = m10;
            m10 = T00 * M0;
            m11 = T01 * M0;
            m12 += T02 * M0;
            break;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SCALE): 
            M0 = m00;
            m00 = T00 * M0;
            m01 = T01 * M0;
            m02 += T02 * M0;
            M0 = m11;
            m10 = T10 * M0;
            m11 = T11 * M0;
            m12 += T12 * M0;
            break;
        
        case (APPLY_TRANSLATE): 
            m00 = T00;
            m01 = T01;
            m02 += T02;
            m10 = T10;
            m11 = T11;
            m12 += T12;
            state = txstate | APPLY_TRANSLATE;
            type = TYPE_UNKNOWN;
            return;
        
        }
        updateState();
    }
    
    public void preConcatenate(AffineTransform Tx) {
        double M0;
        double M1;
        double T00;
        double T01;
        double T10;
        double T11;
        double T02;
        double T12;
        int mystate = state;
        int txstate = Tx.state;
        switch ((txstate << HI_SHIFT) | mystate) {
        case (HI_IDENTITY | APPLY_IDENTITY): 
        
        case (HI_IDENTITY | APPLY_TRANSLATE): 
        
        case (HI_IDENTITY | APPLY_SCALE): 
        
        case (HI_IDENTITY | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_IDENTITY | APPLY_SHEAR): 
        
        case (HI_IDENTITY | APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_IDENTITY | APPLY_SHEAR | APPLY_SCALE): 
        
        case (HI_IDENTITY | APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            return;
        
        case (HI_TRANSLATE | APPLY_IDENTITY): 
        
        case (HI_TRANSLATE | APPLY_SCALE): 
        
        case (HI_TRANSLATE | APPLY_SHEAR): 
        
        case (HI_TRANSLATE | APPLY_SHEAR | APPLY_SCALE): 
            m02 = Tx.m02;
            m12 = Tx.m12;
            state = mystate | APPLY_TRANSLATE;
            type |= TYPE_TRANSLATION;
            return;
        
        case (HI_TRANSLATE | APPLY_TRANSLATE): 
        
        case (HI_TRANSLATE | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_TRANSLATE | APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_TRANSLATE | APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            m02 = m02 + Tx.m02;
            m12 = m12 + Tx.m12;
            return;
        
        case (HI_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SCALE | APPLY_IDENTITY): 
            state = mystate | APPLY_SCALE;
        
        case (HI_SCALE | APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SCALE | APPLY_SHEAR | APPLY_SCALE): 
        
        case (HI_SCALE | APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_SCALE | APPLY_SHEAR): 
        
        case (HI_SCALE | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SCALE | APPLY_SCALE): 
            T00 = Tx.m00;
            T11 = Tx.m11;
            if ((mystate & APPLY_SHEAR) != 0) {
                m01 = m01 * T00;
                m10 = m10 * T11;
                if ((mystate & APPLY_SCALE) != 0) {
                    m00 = m00 * T00;
                    m11 = m11 * T11;
                }
            } else {
                m00 = m00 * T00;
                m11 = m11 * T11;
            }
            if ((mystate & APPLY_TRANSLATE) != 0) {
                m02 = m02 * T00;
                m12 = m12 * T11;
            }
            type = TYPE_UNKNOWN;
            return;
        
        case (HI_SHEAR | APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_SHEAR | APPLY_SHEAR): 
            mystate = mystate | APPLY_SCALE;
        
        case (HI_SHEAR | APPLY_TRANSLATE): 
        
        case (HI_SHEAR | APPLY_IDENTITY): 
        
        case (HI_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SHEAR | APPLY_SCALE): 
            state = mystate ^ APPLY_SHEAR;
        
        case (HI_SHEAR | APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (HI_SHEAR | APPLY_SHEAR | APPLY_SCALE): 
            T01 = Tx.m01;
            T10 = Tx.m10;
            M0 = m00;
            m00 = m10 * T01;
            m10 = M0 * T10;
            M0 = m01;
            m01 = m11 * T01;
            m11 = M0 * T10;
            M0 = m02;
            m02 = m12 * T01;
            m12 = M0 * T10;
            type = TYPE_UNKNOWN;
            return;
        
        }
        T00 = Tx.m00;
        T01 = Tx.m01;
        T02 = Tx.m02;
        T10 = Tx.m10;
        T11 = Tx.m11;
        T12 = Tx.m12;
        switch (mystate) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            M0 = m02;
            M1 = m12;
            T02 += M0 * T00 + M1 * T01;
            T12 += M0 * T10 + M1 * T11;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            m02 = T02;
            m12 = T12;
            M0 = m00;
            M1 = m10;
            m00 = M0 * T00 + M1 * T01;
            m10 = M0 * T10 + M1 * T11;
            M0 = m01;
            M1 = m11;
            m01 = M0 * T00 + M1 * T01;
            m11 = M0 * T10 + M1 * T11;
            break;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            M0 = m02;
            M1 = m12;
            T02 += M0 * T00 + M1 * T01;
            T12 += M0 * T10 + M1 * T11;
        
        case (APPLY_SHEAR): 
            m02 = T02;
            m12 = T12;
            M0 = m10;
            m00 = M0 * T01;
            m10 = M0 * T11;
            M0 = m01;
            m01 = M0 * T00;
            m11 = M0 * T10;
            break;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            M0 = m02;
            M1 = m12;
            T02 += M0 * T00 + M1 * T01;
            T12 += M0 * T10 + M1 * T11;
        
        case (APPLY_SCALE): 
            m02 = T02;
            m12 = T12;
            M0 = m00;
            m00 = M0 * T00;
            m10 = M0 * T10;
            M0 = m11;
            m01 = M0 * T01;
            m11 = M0 * T11;
            break;
        
        case (APPLY_TRANSLATE): 
            M0 = m02;
            M1 = m12;
            T02 += M0 * T00 + M1 * T01;
            T12 += M0 * T10 + M1 * T11;
        
        case (APPLY_IDENTITY): 
            m02 = T02;
            m12 = T12;
            m00 = T00;
            m10 = T10;
            m01 = T01;
            m11 = T11;
            state = mystate | txstate;
            type = TYPE_UNKNOWN;
            return;
        
        }
        updateState();
    }
    
    public AffineTransform createInverse() throws NoninvertibleTransformException {
        double det;
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            det = m00 * m11 - m01 * m10;
            if (Math.abs(det) <= Double.MIN_VALUE) {
                throw new NoninvertibleTransformException("Determinant is " + det);
            }
            return new AffineTransform(m11 / det, -m10 / det, -m01 / det, m00 / det, (m01 * m12 - m11 * m02) / det, (m10 * m02 - m00 * m12) / det, (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE));
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            det = m00 * m11 - m01 * m10;
            if (Math.abs(det) <= Double.MIN_VALUE) {
                throw new NoninvertibleTransformException("Determinant is " + det);
            }
            return new AffineTransform(m11 / det, -m10 / det, -m01 / det, m00 / det, 0.0, 0.0, (APPLY_SHEAR | APPLY_SCALE));
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            if (m01 == 0.0 || m10 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            return new AffineTransform(0.0, 1.0 / m01, 1.0 / m10, 0.0, -m12 / m10, -m02 / m01, (APPLY_SHEAR | APPLY_TRANSLATE));
        
        case (APPLY_SHEAR): 
            if (m01 == 0.0 || m10 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            return new AffineTransform(0.0, 1.0 / m01, 1.0 / m10, 0.0, 0.0, 0.0, (APPLY_SHEAR));
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            if (m00 == 0.0 || m11 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            return new AffineTransform(1.0 / m00, 0.0, 0.0, 1.0 / m11, -m02 / m00, -m12 / m11, (APPLY_SCALE | APPLY_TRANSLATE));
        
        case (APPLY_SCALE): 
            if (m00 == 0.0 || m11 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            return new AffineTransform(1.0 / m00, 0.0, 0.0, 1.0 / m11, 0.0, 0.0, (APPLY_SCALE));
        
        case (APPLY_TRANSLATE): 
            return new AffineTransform(1.0, 0.0, 0.0, 1.0, -m02, -m12, (APPLY_TRANSLATE));
        
        case (APPLY_IDENTITY): 
            return new AffineTransform();
        
        }
    }
    
    public Point2D transform(Point2D ptSrc, Point2D ptDst) {
        if (ptDst == null) {
            if (ptSrc instanceof Point2D$Double) {
                ptDst = new Point2D$Double();
            } else {
                ptDst = new Point2D$Float();
            }
        }
        double x = ptSrc.getX();
        double y = ptSrc.getY();
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            ptDst.setLocation(x * m00 + y * m01 + m02, x * m10 + y * m11 + m12);
            return ptDst;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            ptDst.setLocation(x * m00 + y * m01, x * m10 + y * m11);
            return ptDst;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            ptDst.setLocation(y * m01 + m02, x * m10 + m12);
            return ptDst;
        
        case (APPLY_SHEAR): 
            ptDst.setLocation(y * m01, x * m10);
            return ptDst;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            ptDst.setLocation(x * m00 + m02, y * m11 + m12);
            return ptDst;
        
        case (APPLY_SCALE): 
            ptDst.setLocation(x * m00, y * m11);
            return ptDst;
        
        case (APPLY_TRANSLATE): 
            ptDst.setLocation(x + m02, y + m12);
            return ptDst;
        
        case (APPLY_IDENTITY): 
            ptDst.setLocation(x, y);
            return ptDst;
        
        }
    }
    
    public void transform(Point2D[] ptSrc, int srcOff, Point2D[] ptDst, int dstOff, int numPts) {
        int state = this.state;
        while (--numPts >= 0) {
            Point2D src = ptSrc[srcOff++];
            double x = src.getX();
            double y = src.getY();
            Point2D dst = ptDst[dstOff++];
            if (dst == null) {
                if (src instanceof Point2D$Double) {
                    dst = new Point2D$Double();
                } else {
                    dst = new Point2D$Float();
                }
                ptDst[dstOff - 1] = dst;
            }
            switch (state) {
            default: 
                stateError();
            
            case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
                dst.setLocation(x * m00 + y * m01 + m02, x * m10 + y * m11 + m12);
                break;
            
            case (APPLY_SHEAR | APPLY_SCALE): 
                dst.setLocation(x * m00 + y * m01, x * m10 + y * m11);
                break;
            
            case (APPLY_SHEAR | APPLY_TRANSLATE): 
                dst.setLocation(y * m01 + m02, x * m10 + m12);
                break;
            
            case (APPLY_SHEAR): 
                dst.setLocation(y * m01, x * m10);
                break;
            
            case (APPLY_SCALE | APPLY_TRANSLATE): 
                dst.setLocation(x * m00 + m02, y * m11 + m12);
                break;
            
            case (APPLY_SCALE): 
                dst.setLocation(x * m00, y * m11);
                break;
            
            case (APPLY_TRANSLATE): 
                dst.setLocation(x + m02, y + m12);
                break;
            
            case (APPLY_IDENTITY): 
                dst.setLocation(x, y);
                break;
            
            }
        }
    }
    
    public void transform(float[] srcPts, int srcOff, float[] dstPts, int dstOff, int numPts) {
        double M00;
        double M01;
        double M02;
        double M10;
        double M11;
        double M12;
        if (dstPts == srcPts && dstOff > srcOff && dstOff < srcOff + numPts * 2) {
            System.arraycopy(srcPts, srcOff, dstPts, dstOff, numPts * 2);
            srcOff = dstOff;
        }
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M11 = m11;
            M12 = m12;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = (float)(M00 * x + M01 * y + M02);
                dstPts[dstOff++] = (float)(M10 * x + M11 * y + M12);
            }
            return;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            M00 = m00;
            M01 = m01;
            M10 = m10;
            M11 = m11;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = (float)(M00 * x + M01 * y);
                dstPts[dstOff++] = (float)(M10 * x + M11 * y);
            }
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M12 = m12;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = (float)(M01 * srcPts[srcOff++] + M02);
                dstPts[dstOff++] = (float)(M10 * x + M12);
            }
            return;
        
        case (APPLY_SHEAR): 
            M01 = m01;
            M10 = m10;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = (float)(M01 * srcPts[srcOff++]);
                dstPts[dstOff++] = (float)(M10 * x);
            }
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M02 = m02;
            M11 = m11;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = (float)(M00 * srcPts[srcOff++] + M02);
                dstPts[dstOff++] = (float)(M11 * srcPts[srcOff++] + M12);
            }
            return;
        
        case (APPLY_SCALE): 
            M00 = m00;
            M11 = m11;
            while (--numPts >= 0) {
                dstPts[dstOff++] = (float)(M00 * srcPts[srcOff++]);
                dstPts[dstOff++] = (float)(M11 * srcPts[srcOff++]);
            }
            return;
        
        case (APPLY_TRANSLATE): 
            M02 = m02;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = (float)(srcPts[srcOff++] + M02);
                dstPts[dstOff++] = (float)(srcPts[srcOff++] + M12);
            }
            return;
        
        case (APPLY_IDENTITY): 
            if (srcPts != dstPts || srcOff != dstOff) {
                System.arraycopy(srcPts, srcOff, dstPts, dstOff, numPts * 2);
            }
            return;
        
        }
    }
    
    public void transform(double[] srcPts, int srcOff, double[] dstPts, int dstOff, int numPts) {
        double M00;
        double M01;
        double M02;
        double M10;
        double M11;
        double M12;
        if (dstPts == srcPts && dstOff > srcOff && dstOff < srcOff + numPts * 2) {
            System.arraycopy(srcPts, srcOff, dstPts, dstOff, numPts * 2);
            srcOff = dstOff;
        }
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M11 = m11;
            M12 = m12;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = M00 * x + M01 * y + M02;
                dstPts[dstOff++] = M10 * x + M11 * y + M12;
            }
            return;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            M00 = m00;
            M01 = m01;
            M10 = m10;
            M11 = m11;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = M00 * x + M01 * y;
                dstPts[dstOff++] = M10 * x + M11 * y;
            }
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M12 = m12;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = M01 * srcPts[srcOff++] + M02;
                dstPts[dstOff++] = M10 * x + M12;
            }
            return;
        
        case (APPLY_SHEAR): 
            M01 = m01;
            M10 = m10;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = M01 * srcPts[srcOff++];
                dstPts[dstOff++] = M10 * x;
            }
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M02 = m02;
            M11 = m11;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = M00 * srcPts[srcOff++] + M02;
                dstPts[dstOff++] = M11 * srcPts[srcOff++] + M12;
            }
            return;
        
        case (APPLY_SCALE): 
            M00 = m00;
            M11 = m11;
            while (--numPts >= 0) {
                dstPts[dstOff++] = M00 * srcPts[srcOff++];
                dstPts[dstOff++] = M11 * srcPts[srcOff++];
            }
            return;
        
        case (APPLY_TRANSLATE): 
            M02 = m02;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = srcPts[srcOff++] + M02;
                dstPts[dstOff++] = srcPts[srcOff++] + M12;
            }
            return;
        
        case (APPLY_IDENTITY): 
            if (srcPts != dstPts || srcOff != dstOff) {
                System.arraycopy(srcPts, srcOff, dstPts, dstOff, numPts * 2);
            }
            return;
        
        }
    }
    
    public void transform(float[] srcPts, int srcOff, double[] dstPts, int dstOff, int numPts) {
        double M00;
        double M01;
        double M02;
        double M10;
        double M11;
        double M12;
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M11 = m11;
            M12 = m12;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = M00 * x + M01 * y + M02;
                dstPts[dstOff++] = M10 * x + M11 * y + M12;
            }
            return;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            M00 = m00;
            M01 = m01;
            M10 = m10;
            M11 = m11;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = M00 * x + M01 * y;
                dstPts[dstOff++] = M10 * x + M11 * y;
            }
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M12 = m12;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = M01 * srcPts[srcOff++] + M02;
                dstPts[dstOff++] = M10 * x + M12;
            }
            return;
        
        case (APPLY_SHEAR): 
            M01 = m01;
            M10 = m10;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = M01 * srcPts[srcOff++];
                dstPts[dstOff++] = M10 * x;
            }
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M02 = m02;
            M11 = m11;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = M00 * srcPts[srcOff++] + M02;
                dstPts[dstOff++] = M11 * srcPts[srcOff++] + M12;
            }
            return;
        
        case (APPLY_SCALE): 
            M00 = m00;
            M11 = m11;
            while (--numPts >= 0) {
                dstPts[dstOff++] = M00 * srcPts[srcOff++];
                dstPts[dstOff++] = M11 * srcPts[srcOff++];
            }
            return;
        
        case (APPLY_TRANSLATE): 
            M02 = m02;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = srcPts[srcOff++] + M02;
                dstPts[dstOff++] = srcPts[srcOff++] + M12;
            }
            return;
        
        case (APPLY_IDENTITY): 
            while (--numPts >= 0) {
                dstPts[dstOff++] = srcPts[srcOff++];
                dstPts[dstOff++] = srcPts[srcOff++];
            }
            return;
        
        }
    }
    
    public void transform(double[] srcPts, int srcOff, float[] dstPts, int dstOff, int numPts) {
        double M00;
        double M01;
        double M02;
        double M10;
        double M11;
        double M12;
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M11 = m11;
            M12 = m12;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = (float)(M00 * x + M01 * y + M02);
                dstPts[dstOff++] = (float)(M10 * x + M11 * y + M12);
            }
            return;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            M00 = m00;
            M01 = m01;
            M10 = m10;
            M11 = m11;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = (float)(M00 * x + M01 * y);
                dstPts[dstOff++] = (float)(M10 * x + M11 * y);
            }
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M12 = m12;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = (float)(M01 * srcPts[srcOff++] + M02);
                dstPts[dstOff++] = (float)(M10 * x + M12);
            }
            return;
        
        case (APPLY_SHEAR): 
            M01 = m01;
            M10 = m10;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = (float)(M01 * srcPts[srcOff++]);
                dstPts[dstOff++] = (float)(M10 * x);
            }
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M02 = m02;
            M11 = m11;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = (float)(M00 * srcPts[srcOff++] + M02);
                dstPts[dstOff++] = (float)(M11 * srcPts[srcOff++] + M12);
            }
            return;
        
        case (APPLY_SCALE): 
            M00 = m00;
            M11 = m11;
            while (--numPts >= 0) {
                dstPts[dstOff++] = (float)(M00 * srcPts[srcOff++]);
                dstPts[dstOff++] = (float)(M11 * srcPts[srcOff++]);
            }
            return;
        
        case (APPLY_TRANSLATE): 
            M02 = m02;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = (float)(srcPts[srcOff++] + M02);
                dstPts[dstOff++] = (float)(srcPts[srcOff++] + M12);
            }
            return;
        
        case (APPLY_IDENTITY): 
            while (--numPts >= 0) {
                dstPts[dstOff++] = (float)(srcPts[srcOff++]);
                dstPts[dstOff++] = (float)(srcPts[srcOff++]);
            }
            return;
        
        }
    }
    
    public Point2D inverseTransform(Point2D ptSrc, Point2D ptDst) throws NoninvertibleTransformException {
        if (ptDst == null) {
            if (ptSrc instanceof Point2D$Double) {
                ptDst = new Point2D$Double();
            } else {
                ptDst = new Point2D$Float();
            }
        }
        double x = ptSrc.getX();
        double y = ptSrc.getY();
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            x -= m02;
            y -= m12;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            double det = m00 * m11 - m01 * m10;
            if (Math.abs(det) <= Double.MIN_VALUE) {
                throw new NoninvertibleTransformException("Determinant is " + det);
            }
            ptDst.setLocation((x * m11 - y * m01) / det, (y * m00 - x * m10) / det);
            return ptDst;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            x -= m02;
            y -= m12;
        
        case (APPLY_SHEAR): 
            if (m01 == 0.0 || m10 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            ptDst.setLocation(y / m10, x / m01);
            return ptDst;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            x -= m02;
            y -= m12;
        
        case (APPLY_SCALE): 
            if (m00 == 0.0 || m11 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            ptDst.setLocation(x / m00, y / m11);
            return ptDst;
        
        case (APPLY_TRANSLATE): 
            ptDst.setLocation(x - m02, y - m12);
            return ptDst;
        
        case (APPLY_IDENTITY): 
            ptDst.setLocation(x, y);
            return ptDst;
        
        }
    }
    
    public void inverseTransform(double[] srcPts, int srcOff, double[] dstPts, int dstOff, int numPts) throws NoninvertibleTransformException {
        double M00;
        double M01;
        double M02;
        double M10;
        double M11;
        double M12;
        double det;
        if (dstPts == srcPts && dstOff > srcOff && dstOff < srcOff + numPts * 2) {
            System.arraycopy(srcPts, srcOff, dstPts, dstOff, numPts * 2);
            srcOff = dstOff;
        }
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M11 = m11;
            M12 = m12;
            det = M00 * M11 - M01 * M10;
            if (Math.abs(det) <= Double.MIN_VALUE) {
                throw new NoninvertibleTransformException("Determinant is " + det);
            }
            while (--numPts >= 0) {
                double x = srcPts[srcOff++] - M02;
                double y = srcPts[srcOff++] - M12;
                dstPts[dstOff++] = (x * M11 - y * M01) / det;
                dstPts[dstOff++] = (y * M00 - x * M10) / det;
            }
            return;
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            M00 = m00;
            M01 = m01;
            M10 = m10;
            M11 = m11;
            det = M00 * M11 - M01 * M10;
            if (Math.abs(det) <= Double.MIN_VALUE) {
                throw new NoninvertibleTransformException("Determinant is " + det);
            }
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = (x * M11 - y * M01) / det;
                dstPts[dstOff++] = (y * M00 - x * M10) / det;
            }
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
            M01 = m01;
            M02 = m02;
            M10 = m10;
            M12 = m12;
            if (M01 == 0.0 || M10 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            while (--numPts >= 0) {
                double x = srcPts[srcOff++] - M02;
                dstPts[dstOff++] = (srcPts[srcOff++] - M12) / M10;
                dstPts[dstOff++] = x / M01;
            }
            return;
        
        case (APPLY_SHEAR): 
            M01 = m01;
            M10 = m10;
            if (M01 == 0.0 || M10 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = srcPts[srcOff++] / M10;
                dstPts[dstOff++] = x / M01;
            }
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
            M00 = m00;
            M02 = m02;
            M11 = m11;
            M12 = m12;
            if (M00 == 0.0 || M11 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            while (--numPts >= 0) {
                dstPts[dstOff++] = (srcPts[srcOff++] - M02) / M00;
                dstPts[dstOff++] = (srcPts[srcOff++] - M12) / M11;
            }
            return;
        
        case (APPLY_SCALE): 
            M00 = m00;
            M11 = m11;
            if (M00 == 0.0 || M11 == 0.0) {
                throw new NoninvertibleTransformException("Determinant is 0");
            }
            while (--numPts >= 0) {
                dstPts[dstOff++] = srcPts[srcOff++] / M00;
                dstPts[dstOff++] = srcPts[srcOff++] / M11;
            }
            return;
        
        case (APPLY_TRANSLATE): 
            M02 = m02;
            M12 = m12;
            while (--numPts >= 0) {
                dstPts[dstOff++] = srcPts[srcOff++] - M02;
                dstPts[dstOff++] = srcPts[srcOff++] - M12;
            }
            return;
        
        case (APPLY_IDENTITY): 
            if (srcPts != dstPts || srcOff != dstOff) {
                System.arraycopy(srcPts, srcOff, dstPts, dstOff, numPts * 2);
            }
            return;
        
        }
    }
    
    public Point2D deltaTransform(Point2D ptSrc, Point2D ptDst) {
        if (ptDst == null) {
            if (ptSrc instanceof Point2D$Double) {
                ptDst = new Point2D$Double();
            } else {
                ptDst = new Point2D$Float();
            }
        }
        double x = ptSrc.getX();
        double y = ptSrc.getY();
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            ptDst.setLocation(x * m00 + y * m01, x * m10 + y * m11);
            return ptDst;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR): 
            ptDst.setLocation(y * m01, x * m10);
            return ptDst;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SCALE): 
            ptDst.setLocation(x * m00, y * m11);
            return ptDst;
        
        case (APPLY_TRANSLATE): 
        
        case (APPLY_IDENTITY): 
            ptDst.setLocation(x, y);
            return ptDst;
        
        }
    }
    
    public void deltaTransform(double[] srcPts, int srcOff, double[] dstPts, int dstOff, int numPts) {
        double M00;
        double M01;
        double M10;
        double M11;
        if (dstPts == srcPts && dstOff > srcOff && dstOff < srcOff + numPts * 2) {
            System.arraycopy(srcPts, srcOff, dstPts, dstOff, numPts * 2);
            srcOff = dstOff;
        }
        switch (state) {
        default: 
            stateError();
        
        case (APPLY_SHEAR | APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR | APPLY_SCALE): 
            M00 = m00;
            M01 = m01;
            M10 = m10;
            M11 = m11;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                double y = srcPts[srcOff++];
                dstPts[dstOff++] = x * M00 + y * M01;
                dstPts[dstOff++] = x * M10 + y * M11;
            }
            return;
        
        case (APPLY_SHEAR | APPLY_TRANSLATE): 
        
        case (APPLY_SHEAR): 
            M01 = m01;
            M10 = m10;
            while (--numPts >= 0) {
                double x = srcPts[srcOff++];
                dstPts[dstOff++] = srcPts[srcOff++] * M01;
                dstPts[dstOff++] = x * M10;
            }
            return;
        
        case (APPLY_SCALE | APPLY_TRANSLATE): 
        
        case (APPLY_SCALE): 
            M00 = m00;
            M11 = m11;
            while (--numPts >= 0) {
                dstPts[dstOff++] = srcPts[srcOff++] * M00;
                dstPts[dstOff++] = srcPts[srcOff++] * M11;
            }
            return;
        
        case (APPLY_TRANSLATE): 
        
        case (APPLY_IDENTITY): 
            if (srcPts != dstPts || srcOff != dstOff) {
                System.arraycopy(srcPts, srcOff, dstPts, dstOff, numPts * 2);
            }
            return;
        
        }
    }
    
    public Shape createTransformedShape(Shape pSrc) {
        if (pSrc == null) {
            return null;
        }
        if (pSrc instanceof GeneralPath) {
            return ((GeneralPath)(GeneralPath)pSrc).createTransformedShape(this);
        } else {
            PathIterator pi = pSrc.getPathIterator(this);
            GeneralPath gp = new GeneralPath(pi.getWindingRule());
            gp.append(pi, false);
            return gp;
        }
    }
    
    private static double _matround(double matval) {
        return Math.rint(matval * 1.0E15) / 1.0E15;
    }
    
    public String toString() {
        return ("AffineTransform[[" + _matround(m00) + ", " + _matround(m01) + ", " + _matround(m02) + "], [" + _matround(m10) + ", " + _matround(m11) + ", " + _matround(m12) + "]]");
    }
    
    public boolean isIdentity() {
        return (state == APPLY_IDENTITY || (getType() == TYPE_IDENTITY));
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public int hashCode() {
        long bits = Double.doubleToLongBits(m00);
        bits = bits * 31 + Double.doubleToLongBits(m01);
        bits = bits * 31 + Double.doubleToLongBits(m02);
        bits = bits * 31 + Double.doubleToLongBits(m10);
        bits = bits * 31 + Double.doubleToLongBits(m11);
        bits = bits * 31 + Double.doubleToLongBits(m12);
        return (((int)bits) ^ ((int)(bits >> 32)));
    }
    
    public boolean equals(Object obj) {
        if (!(obj instanceof AffineTransform)) {
            return false;
        }
        AffineTransform a = (AffineTransform)(AffineTransform)obj;
        return ((m00 == a.m00) && (m01 == a.m01) && (m02 == a.m02) && (m10 == a.m10) && (m11 == a.m11) && (m12 == a.m12));
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws java.lang.ClassNotFoundException, java.io.IOException {
        s.defaultWriteObject();
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.lang.ClassNotFoundException, java.io.IOException {
        s.defaultReadObject();
        updateState();
    }
}
