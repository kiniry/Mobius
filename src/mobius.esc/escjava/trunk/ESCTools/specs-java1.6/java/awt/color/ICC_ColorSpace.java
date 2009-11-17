package java.awt.color;

import sun.awt.color.ICC_Transform;

public class ICC_ColorSpace extends ColorSpace {
    static final long serialVersionUID = 3455889114070431483L;
    private ICC_Profile thisProfile;
    private float[] minVal;
    private float[] maxVal;
    private float[] diffMinMax;
    private float[] invDiffMinMax;
    private boolean needScaleInit = true;
    private transient ICC_Transform this2srgb;
    private transient ICC_Transform srgb2this;
    private transient ICC_Transform this2xyz;
    private transient ICC_Transform xyz2this;
    
    public ICC_ColorSpace(ICC_Profile profile) {
        super(profile.getColorSpaceType(), profile.getNumComponents());
        int profileClass = profile.getProfileClass();
        if ((profileClass != ICC_Profile.CLASS_INPUT) && (profileClass != ICC_Profile.CLASS_DISPLAY) && (profileClass != ICC_Profile.CLASS_OUTPUT) && (profileClass != ICC_Profile.CLASS_COLORSPACECONVERSION) && (profileClass != ICC_Profile.CLASS_NAMEDCOLOR)) {
            throw new IllegalArgumentException("Invalid profile type");
        }
        thisProfile = profile;
        setMinMax();
    }
    
    public ICC_Profile getProfile() {
        return thisProfile;
    }
    
    public float[] toRGB(float[] colorvalue) {
        if (this2srgb == null) {
            ICC_Transform[] transformList = new ICC_Transform[2];
            ICC_ColorSpace srgbCS = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(CS_sRGB);
            transformList[0] = new ICC_Transform(thisProfile, ICC_Transform.Any, ICC_Transform.In);
            transformList[1] = new ICC_Transform(srgbCS.getProfile(), ICC_Transform.Any, ICC_Transform.Out);
            this2srgb = new ICC_Transform(transformList);
            if (needScaleInit) {
                setComponentScaling();
            }
        }
        int nc = this.getNumComponents();
        short[] tmp = new short[nc];
        for (int i = 0; i < nc; i++) {
            tmp[i] = (short)((colorvalue[i] - minVal[i]) * invDiffMinMax[i] + 0.5F);
        }
        tmp = this2srgb.colorConvert(tmp, null);
        float[] result = new float[3];
        for (int i = 0; i < 3; i++) {
            result[i] = ((float)(tmp[i] & 65535)) / 65535.0F;
        }
        return result;
    }
    
    public float[] fromRGB(float[] rgbvalue) {
        if (srgb2this == null) {
            ICC_Transform[] transformList = new ICC_Transform[2];
            ICC_ColorSpace srgbCS = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(CS_sRGB);
            transformList[0] = new ICC_Transform(srgbCS.getProfile(), ICC_Transform.Any, ICC_Transform.In);
            transformList[1] = new ICC_Transform(thisProfile, ICC_Transform.Any, ICC_Transform.Out);
            srgb2this = new ICC_Transform(transformList);
            if (needScaleInit) {
                setComponentScaling();
            }
        }
        short[] tmp = new short[3];
        for (int i = 0; i < 3; i++) {
            tmp[i] = (short)((rgbvalue[i] * 65535.0F) + 0.5F);
        }
        tmp = srgb2this.colorConvert(tmp, null);
        int nc = this.getNumComponents();
        float[] result = new float[nc];
        for (int i = 0; i < nc; i++) {
            result[i] = (((float)(tmp[i] & 65535)) / 65535.0F) * diffMinMax[i] + minVal[i];
        }
        return result;
    }
    
    public float[] toCIEXYZ(float[] colorvalue) {
        if (this2xyz == null) {
            ICC_Transform[] transformList = new ICC_Transform[2];
            ICC_ColorSpace xyzCS = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(CS_CIEXYZ);
            try {
                transformList[0] = new ICC_Transform(thisProfile, ICC_Profile.icRelativeColorimetric, ICC_Transform.In);
            } catch (CMMException e) {
                transformList[0] = new ICC_Transform(thisProfile, ICC_Transform.Any, ICC_Transform.In);
            }
            transformList[1] = new ICC_Transform(xyzCS.getProfile(), ICC_Transform.Any, ICC_Transform.Out);
            this2xyz = new ICC_Transform(transformList);
            if (needScaleInit) {
                setComponentScaling();
            }
        }
        int nc = this.getNumComponents();
        short[] tmp = new short[nc];
        for (int i = 0; i < nc; i++) {
            tmp[i] = (short)((colorvalue[i] - minVal[i]) * invDiffMinMax[i] + 0.5F);
        }
        tmp = this2xyz.colorConvert(tmp, null);
        float ALMOST_TWO = 1.0F + (32767.0F / 32768.0F);
        float[] result = new float[3];
        for (int i = 0; i < 3; i++) {
            result[i] = (((float)(tmp[i] & 65535)) / 65535.0F) * ALMOST_TWO;
        }
        return result;
    }
    
    public float[] fromCIEXYZ(float[] colorvalue) {
        if (xyz2this == null) {
            ICC_Transform[] transformList = new ICC_Transform[2];
            ICC_ColorSpace xyzCS = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(CS_CIEXYZ);
            transformList[0] = new ICC_Transform(xyzCS.getProfile(), ICC_Transform.Any, ICC_Transform.In);
            try {
                transformList[1] = new ICC_Transform(thisProfile, ICC_Profile.icRelativeColorimetric, ICC_Transform.Out);
            } catch (CMMException e) {
                transformList[1] = new ICC_Transform(thisProfile, ICC_Transform.Any, ICC_Transform.Out);
            }
            xyz2this = new ICC_Transform(transformList);
            if (needScaleInit) {
                setComponentScaling();
            }
        }
        short[] tmp = new short[3];
        float ALMOST_TWO = 1.0F + (32767.0F / 32768.0F);
        float factor = 65535.0F / ALMOST_TWO;
        for (int i = 0; i < 3; i++) {
            tmp[i] = (short)((colorvalue[i] * factor) + 0.5F);
        }
        tmp = xyz2this.colorConvert(tmp, null);
        int nc = this.getNumComponents();
        float[] result = new float[nc];
        for (int i = 0; i < nc; i++) {
            result[i] = (((float)(tmp[i] & 65535)) / 65535.0F) * diffMinMax[i] + minVal[i];
        }
        return result;
    }
    
    public float getMinValue(int component) {
        if ((component < 0) || (component > this.getNumComponents() - 1)) {
            throw new IllegalArgumentException("Component index out of range: + component");
        }
        return minVal[component];
    }
    
    public float getMaxValue(int component) {
        if ((component < 0) || (component > this.getNumComponents() - 1)) {
            throw new IllegalArgumentException("Component index out of range: + component");
        }
        return maxVal[component];
    }
    
    private void setMinMax() {
        int nc = this.getNumComponents();
        int type = this.getType();
        minVal = new float[nc];
        maxVal = new float[nc];
        if (type == ColorSpace.TYPE_Lab) {
            minVal[0] = 0.0F;
            maxVal[0] = 100.0F;
            minVal[1] = -128.0F;
            maxVal[1] = 127.0F;
            minVal[2] = -128.0F;
            maxVal[2] = 127.0F;
        } else if (type == ColorSpace.TYPE_XYZ) {
            minVal[0] = minVal[1] = minVal[2] = 0.0F;
            maxVal[0] = maxVal[1] = maxVal[2] = 1.0F + (32767.0F / 32768.0F);
        } else {
            for (int i = 0; i < nc; i++) {
                minVal[i] = 0.0F;
                maxVal[i] = 1.0F;
            }
        }
    }
    
    private void setComponentScaling() {
        int nc = this.getNumComponents();
        diffMinMax = new float[nc];
        invDiffMinMax = new float[nc];
        for (int i = 0; i < nc; i++) {
            minVal[i] = this.getMinValue(i);
            maxVal[i] = this.getMaxValue(i);
            diffMinMax[i] = maxVal[i] - minVal[i];
            invDiffMinMax[i] = 65535.0F / diffMinMax[i];
        }
        needScaleInit = false;
    }
}
