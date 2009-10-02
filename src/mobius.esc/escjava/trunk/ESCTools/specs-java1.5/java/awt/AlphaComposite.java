package java.awt;

import java.awt.image.ColorModel;
import sun.java2d.SunCompositeContext;

public final class AlphaComposite implements Composite {
    public static final int CLEAR = 1;
    public static final int SRC = 2;
    public static final int DST = 9;
    public static final int SRC_OVER = 3;
    public static final int DST_OVER = 4;
    public static final int SRC_IN = 5;
    public static final int DST_IN = 6;
    public static final int SRC_OUT = 7;
    public static final int DST_OUT = 8;
    public static final int SRC_ATOP = 10;
    public static final int DST_ATOP = 11;
    public static final int XOR = 12;
    public static final AlphaComposite Clear = new AlphaComposite(CLEAR);
    public static final AlphaComposite Src = new AlphaComposite(SRC);
    public static final AlphaComposite Dst = new AlphaComposite(DST);
    public static final AlphaComposite SrcOver = new AlphaComposite(SRC_OVER);
    public static final AlphaComposite DstOver = new AlphaComposite(DST_OVER);
    public static final AlphaComposite SrcIn = new AlphaComposite(SRC_IN);
    public static final AlphaComposite DstIn = new AlphaComposite(DST_IN);
    public static final AlphaComposite SrcOut = new AlphaComposite(SRC_OUT);
    public static final AlphaComposite DstOut = new AlphaComposite(DST_OUT);
    public static final AlphaComposite SrcAtop = new AlphaComposite(SRC_ATOP);
    public static final AlphaComposite DstAtop = new AlphaComposite(DST_ATOP);
    public static final AlphaComposite Xor = new AlphaComposite(XOR);
    private static final int MIN_RULE = CLEAR;
    private static final int MAX_RULE = XOR;
    float extraAlpha;
    int rule;
    
    private AlphaComposite(int rule) {
        this(rule, 1.0F);
    }
    
    private AlphaComposite(int rule, float alpha) {
        
        if (alpha < 0.0F || alpha > 1.0F) {
            throw new IllegalArgumentException("alpha value out of range");
        }
        if (rule < MIN_RULE || rule > MAX_RULE) {
            throw new IllegalArgumentException("unknown composite rule");
        }
        this.rule = rule;
        this.extraAlpha = alpha;
    }
    
    public static AlphaComposite getInstance(int rule) {
        switch (rule) {
        case CLEAR: 
            return Clear;
        
        case SRC: 
            return Src;
        
        case DST: 
            return Dst;
        
        case SRC_OVER: 
            return SrcOver;
        
        case DST_OVER: 
            return DstOver;
        
        case SRC_IN: 
            return SrcIn;
        
        case DST_IN: 
            return DstIn;
        
        case SRC_OUT: 
            return SrcOut;
        
        case DST_OUT: 
            return DstOut;
        
        case SRC_ATOP: 
            return SrcAtop;
        
        case DST_ATOP: 
            return DstAtop;
        
        case XOR: 
            return Xor;
        
        default: 
            throw new IllegalArgumentException("unknown composite rule");
        
        }
    }
    
    public static AlphaComposite getInstance(int rule, float alpha) {
        if (alpha == 1.0F) {
            return getInstance(rule);
        }
        return new AlphaComposite(rule, alpha);
    }
    
    public CompositeContext createContext(ColorModel srcColorModel, ColorModel dstColorModel, RenderingHints hints) {
        return new SunCompositeContext(this, srcColorModel, dstColorModel);
    }
    
    public float getAlpha() {
        return extraAlpha;
    }
    
    public int getRule() {
        return rule;
    }
    
    public int hashCode() {
        return (Float.floatToIntBits(extraAlpha) * 31 + rule);
    }
    
    public boolean equals(Object obj) {
        if (!(obj instanceof AlphaComposite)) {
            return false;
        }
        AlphaComposite ac = (AlphaComposite)(AlphaComposite)obj;
        if (rule != ac.rule) {
            return false;
        }
        if (extraAlpha != ac.extraAlpha) {
            return false;
        }
        return true;
    }
}
