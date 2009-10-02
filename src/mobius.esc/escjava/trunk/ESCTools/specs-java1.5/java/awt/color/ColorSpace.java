package java.awt.color;

import sun.awt.color.CMM;

public abstract class ColorSpace implements java.io.Serializable {
    static final long serialVersionUID = -409452704308689724L;
    private int type;
    private int numComponents;
    private static ColorSpace sRGBspace;
    private static ColorSpace XYZspace;
    private static ColorSpace PYCCspace;
    private static ColorSpace GRAYspace;
    private static ColorSpace LINEAR_RGBspace;
    public static final int TYPE_XYZ = 0;
    public static final int TYPE_Lab = 1;
    public static final int TYPE_Luv = 2;
    public static final int TYPE_YCbCr = 3;
    public static final int TYPE_Yxy = 4;
    public static final int TYPE_RGB = 5;
    public static final int TYPE_GRAY = 6;
    public static final int TYPE_HSV = 7;
    public static final int TYPE_HLS = 8;
    public static final int TYPE_CMYK = 9;
    public static final int TYPE_CMY = 11;
    public static final int TYPE_2CLR = 12;
    public static final int TYPE_3CLR = 13;
    public static final int TYPE_4CLR = 14;
    public static final int TYPE_5CLR = 15;
    public static final int TYPE_6CLR = 16;
    public static final int TYPE_7CLR = 17;
    public static final int TYPE_8CLR = 18;
    public static final int TYPE_9CLR = 19;
    public static final int TYPE_ACLR = 20;
    public static final int TYPE_BCLR = 21;
    public static final int TYPE_CCLR = 22;
    public static final int TYPE_DCLR = 23;
    public static final int TYPE_ECLR = 24;
    public static final int TYPE_FCLR = 25;
    public static final int CS_sRGB = 1000;
    public static final int CS_LINEAR_RGB = 1004;
    public static final int CS_CIEXYZ = 1001;
    public static final int CS_PYCC = 1002;
    public static final int CS_GRAY = 1003;
    
    protected ColorSpace(int type, int numcomponents) {
        
        this.type = type;
        this.numComponents = numcomponents;
    }
    
    public static ColorSpace getInstance(int colorspace) {
        ColorSpace theColorSpace;
        switch (colorspace) {
        case CS_sRGB: 
            synchronized (ColorSpace.class) {
                if (sRGBspace == null) {
                    ICC_Profile theProfile = ICC_Profile.getInstance(CS_sRGB);
                    sRGBspace = new ICC_ColorSpace(theProfile);
                }
                theColorSpace = sRGBspace;
            }
            break;
        
        case CS_CIEXYZ: 
            synchronized (ColorSpace.class) {
                if (XYZspace == null) {
                    ICC_Profile theProfile = ICC_Profile.getInstance(CS_CIEXYZ);
                    XYZspace = new ICC_ColorSpace(theProfile);
                }
                theColorSpace = XYZspace;
            }
            break;
        
        case CS_PYCC: 
            synchronized (ColorSpace.class) {
                if (PYCCspace == null) {
                    ICC_Profile theProfile = ICC_Profile.getInstance(CS_PYCC);
                    PYCCspace = new ICC_ColorSpace(theProfile);
                }
                theColorSpace = PYCCspace;
            }
            break;
        
        case CS_GRAY: 
            synchronized (ColorSpace.class) {
                if (GRAYspace == null) {
                    ICC_Profile theProfile = ICC_Profile.getInstance(CS_GRAY);
                    GRAYspace = new ICC_ColorSpace(theProfile);
                    CMM.GRAYspace = GRAYspace;
                }
                theColorSpace = GRAYspace;
            }
            break;
        
        case CS_LINEAR_RGB: 
            synchronized (ColorSpace.class) {
                if (LINEAR_RGBspace == null) {
                    ICC_Profile theProfile = ICC_Profile.getInstance(CS_LINEAR_RGB);
                    LINEAR_RGBspace = new ICC_ColorSpace(theProfile);
                    CMM.LINEAR_RGBspace = LINEAR_RGBspace;
                }
                theColorSpace = LINEAR_RGBspace;
            }
            break;
        
        default: 
            throw new IllegalArgumentException("Unknown color space");
        
        }
        return theColorSpace;
    }
    
    public boolean isCS_sRGB() {
        return (this == sRGBspace);
    }
    
    public abstract float[] toRGB(float[] colorvalue);
    
    public abstract float[] fromRGB(float[] rgbvalue);
    
    public abstract float[] toCIEXYZ(float[] colorvalue);
    
    public abstract float[] fromCIEXYZ(float[] colorvalue);
    
    public int getType() {
        return type;
    }
    
    public int getNumComponents() {
        return numComponents;
    }
    
    public String getName(int idx) {
        if ((idx < 0) || (idx > numComponents - 1)) {
            throw new IllegalArgumentException("Component index out of range: " + idx);
        }
        return new String("Unnamed color component(" + idx + ")");
    }
    
    public float getMinValue(int component) {
        if ((component < 0) || (component > numComponents - 1)) {
            throw new IllegalArgumentException("Component index out of range: " + component);
        }
        return 0.0F;
    }
    
    public float getMaxValue(int component) {
        if ((component < 0) || (component > numComponents - 1)) {
            throw new IllegalArgumentException("Component index out of range: " + component);
        }
        return 1.0F;
    }
    
    static boolean isCS_CIEXYZ(ColorSpace cspace) {
        return (cspace == XYZspace);
    }
}
