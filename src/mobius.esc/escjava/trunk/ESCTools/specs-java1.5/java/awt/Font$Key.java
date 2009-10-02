package java.awt;

import java.awt.font.TextAttribute;
import java.awt.font.TransformAttribute;
import java.awt.geom.AffineTransform;
import java.io.*;
import java.util.Map;

class Font$Key {
    String family = "Dialog";
    float weight = 1.0F;
    float posture = 0.0F;
    float size = 12.0F;
    int superscript = 0;
    float width = 1.0F;
    double[] txdata = null;
    Map attrs;
    int hashCode = 0;
    
    Font$Key(Map map) {
        
        attrs = map;
        Object o = map.get(TextAttribute.FAMILY);
        if (o != null) {
            family = (String)(String)o;
        }
        hashCode = family.hashCode();
        o = map.get(TextAttribute.WEIGHT);
        if (o != null && o != TextAttribute.WEIGHT_REGULAR) {
            float xweight = ((Float)(Float)o).floatValue();
            if (xweight == TextAttribute.WEIGHT_BOLD.floatValue()) {
                weight = xweight;
                hashCode = (hashCode << 3) ^ Float.floatToIntBits(weight);
            }
        }
        o = map.get(TextAttribute.POSTURE);
        if (o != null && o != TextAttribute.POSTURE_REGULAR) {
            float xposture = ((Float)(Float)o).floatValue();
            if (xposture == TextAttribute.POSTURE_OBLIQUE.floatValue()) {
                posture = xposture;
                hashCode = (hashCode << 3) ^ Float.floatToIntBits(posture);
            }
        }
        o = map.get(TextAttribute.SIZE);
        if (o != null) {
            size = ((Float)(Float)o).floatValue();
            if (size != 12.0F) {
                hashCode = (hashCode << 3) ^ Float.floatToIntBits(size);
            }
        }
        o = map.get(TextAttribute.TRANSFORM);
        if (o != null) {
            AffineTransform tx = null;
            if (o instanceof TransformAttribute) {
                TransformAttribute ta = (TransformAttribute)(TransformAttribute)o;
                if (!ta.isIdentity()) {
                    tx = ta.getTransform();
                }
            } else if (o instanceof AffineTransform) {
                AffineTransform at = (AffineTransform)(AffineTransform)o;
                if (!at.isIdentity()) {
                    tx = at;
                }
            }
            if (tx != null) {
                txdata = new double[6];
                tx.getMatrix(txdata);
                hashCode = (hashCode << 3) ^ new Double(txdata[0]).hashCode();
            }
        }
        o = map.get(TextAttribute.SUPERSCRIPT);
        if (o != null) {
            if (o instanceof Integer) {
                superscript = ((Integer)(Integer)o).intValue();
                hashCode = hashCode << 3 ^ superscript;
            }
        }
        o = map.get(TextAttribute.WIDTH);
        if (o != null) {
            if (o instanceof Float) {
                width = ((Float)(Float)o).floatValue();
                hashCode = hashCode << 3 ^ Float.floatToIntBits(width);
            }
        }
    }
    
    public int hashCode() {
        return hashCode;
    }
    
    public boolean equals(Object rhs) {
        Font$Key rhskey = (Font$Key)(Font$Key)rhs;
        if (this.hashCode == rhskey.hashCode && this.size == rhskey.size && this.weight == rhskey.weight && this.posture == rhskey.posture && this.superscript == rhskey.superscript && this.width == rhskey.width && this.family.equals(rhskey.family) && ((this.txdata == null) == (rhskey.txdata == null))) {
            if (this.txdata != null) {
                for (int i = 0; i < this.txdata.length; ++i) {
                    if (this.txdata[i] != rhskey.txdata[i]) {
                        return false;
                    }
                }
            }
            return true;
        }
        return false;
    }
}
