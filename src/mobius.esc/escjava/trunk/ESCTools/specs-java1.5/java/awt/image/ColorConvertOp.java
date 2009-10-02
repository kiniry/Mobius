package java.awt.image;

import java.awt.Point;
import java.awt.Graphics2D;
import java.awt.color.*;
import sun.awt.color.ICC_Transform;
import sun.awt.color.ProfileDeferralMgr;
import java.awt.geom.Rectangle2D;
import java.awt.geom.Point2D;
import java.awt.RenderingHints;

public class ColorConvertOp implements BufferedImageOp, RasterOp {
    ICC_Profile[] profileList;
    ColorSpace[] CSList;
    ICC_Transform thisTransform;
    ICC_Transform thisRasterTransform;
    ICC_Profile thisSrcProfile;
    ICC_Profile thisDestProfile;
    RenderingHints hints;
    boolean gotProfiles;
    float[] srcMinVals;
    float[] srcMaxVals;
    float[] dstMinVals;
    float[] dstMaxVals;
    static {
        if (ProfileDeferralMgr.deferring) {
            ProfileDeferralMgr.activateProfiles();
        }
    }
    
    public ColorConvertOp(RenderingHints hints) {
        
        profileList = new ICC_Profile[0];
        this.hints = hints;
    }
    
    public ColorConvertOp(ColorSpace cspace, RenderingHints hints) {
        
        if (cspace == null) {
            throw new NullPointerException("ColorSpace cannot be null");
        }
        if (cspace instanceof ICC_ColorSpace) {
            profileList = new ICC_Profile[1];
            profileList[0] = ((ICC_ColorSpace)(ICC_ColorSpace)cspace).getProfile();
        } else {
            CSList = new ColorSpace[1];
            CSList[0] = cspace;
        }
        this.hints = hints;
    }
    
    public ColorConvertOp(ColorSpace srcCspace, ColorSpace dstCspace, RenderingHints hints) {
        
        if ((srcCspace == null) || (dstCspace == null)) {
            throw new NullPointerException("ColorSpaces cannot be null");
        }
        if ((srcCspace instanceof ICC_ColorSpace) && (dstCspace instanceof ICC_ColorSpace)) {
            profileList = new ICC_Profile[2];
            profileList[0] = ((ICC_ColorSpace)(ICC_ColorSpace)srcCspace).getProfile();
            profileList[1] = ((ICC_ColorSpace)(ICC_ColorSpace)dstCspace).getProfile();
            getMinMaxValsFromColorSpaces(srcCspace, dstCspace);
        } else {
            CSList = new ColorSpace[2];
            CSList[0] = srcCspace;
            CSList[1] = dstCspace;
        }
        this.hints = hints;
    }
    
    public ColorConvertOp(ICC_Profile[] profiles, RenderingHints hints) {
        
        if (profiles == null) {
            throw new NullPointerException("Profiles cannot be null");
        }
        gotProfiles = true;
        profileList = new ICC_Profile[profiles.length];
        for (int i1 = 0; i1 < profiles.length; i1++) {
            profileList[i1] = profiles[i1];
        }
        this.hints = hints;
    }
    
    public final ICC_Profile[] getICC_Profiles() {
        if (gotProfiles) {
            ICC_Profile[] profiles = new ICC_Profile[profileList.length];
            for (int i1 = 0; i1 < profileList.length; i1++) {
                profiles[i1] = profileList[i1];
            }
            return profiles;
        }
        return null;
    }
    
    public final BufferedImage filter(BufferedImage src, BufferedImage dest) {
        ColorSpace srcColorSpace;
        ColorSpace destColorSpace;
        BufferedImage savdest = null;
        if (src.getColorModel() instanceof IndexColorModel) {
            IndexColorModel icm = (IndexColorModel)(IndexColorModel)src.getColorModel();
            src = icm.convertToIntDiscrete(src.getRaster(), true);
        }
        srcColorSpace = src.getColorModel().getColorSpace();
        if (dest != null) {
            if (dest.getColorModel() instanceof IndexColorModel) {
                savdest = dest;
                dest = null;
                destColorSpace = null;
            } else {
                destColorSpace = dest.getColorModel().getColorSpace();
            }
        } else {
            destColorSpace = null;
        }
        if ((CSList != null) || (!(srcColorSpace instanceof ICC_ColorSpace)) || ((dest != null) && (!(destColorSpace instanceof ICC_ColorSpace)))) {
            dest = nonICCBIFilter(src, srcColorSpace, dest, destColorSpace);
        } else {
            dest = ICCBIFilter(src, srcColorSpace, dest, destColorSpace);
        }
        if (savdest != null) {
            Graphics2D big = savdest.createGraphics();
            try {
                big.drawImage(dest, 0, 0, null);
            } finally {
                big.dispose();
            }
            return savdest;
        } else {
            return dest;
        }
    }
    
    private final BufferedImage ICCBIFilter(BufferedImage src, ColorSpace srcColorSpace, BufferedImage dest, ColorSpace destColorSpace) {
        int nProfiles = profileList.length;
        ICC_Profile srcProfile = null;
        ICC_Profile destProfile = null;
        srcProfile = ((ICC_ColorSpace)(ICC_ColorSpace)srcColorSpace).getProfile();
        if (dest == null) {
            if (nProfiles == 0) {
                throw new IllegalArgumentException("Destination ColorSpace is undefined");
            }
            destProfile = profileList[nProfiles - 1];
            dest = createCompatibleDestImage(src, null);
        } else {
            if (src.getHeight() != dest.getHeight() || src.getWidth() != dest.getWidth()) {
                throw new IllegalArgumentException("Width or height of BufferedImages do not match");
            }
            destProfile = ((ICC_ColorSpace)(ICC_ColorSpace)destColorSpace).getProfile();
        }
        if ((thisTransform == null) || (thisSrcProfile != srcProfile) || (thisDestProfile != destProfile)) {
            updateBITransform(srcProfile, destProfile);
        }
        thisTransform.colorConvert(src, dest);
        return dest;
    }
    
    private void updateBITransform(ICC_Profile srcProfile, ICC_Profile destProfile) {
        ICC_Profile[] theProfiles;
        int i1;
        int nProfiles;
        int nTransforms;
        int whichTrans;
        int renderState;
        ICC_Transform[] theTransforms;
        boolean useSrc = false;
        boolean useDest = false;
        nProfiles = profileList.length;
        nTransforms = nProfiles;
        if ((nProfiles == 0) || (srcProfile != profileList[0])) {
            nTransforms += 1;
            useSrc = true;
        }
        if ((nProfiles == 0) || (destProfile != profileList[nProfiles - 1]) || (nTransforms < 2)) {
            nTransforms += 1;
            useDest = true;
        }
        theProfiles = new ICC_Profile[nTransforms];
        int idx = 0;
        if (useSrc) {
            theProfiles[idx++] = srcProfile;
        }
        for (i1 = 0; i1 < nProfiles; i1++) {
            theProfiles[idx++] = profileList[i1];
        }
        if (useDest) {
            theProfiles[idx] = destProfile;
        }
        theTransforms = new ICC_Transform[nTransforms];
        if (theProfiles[0].getProfileClass() == ICC_Profile.CLASS_OUTPUT) {
            renderState = ICC_Profile.icRelativeColorimetric;
        } else {
            renderState = ICC_Profile.icPerceptual;
        }
        whichTrans = ICC_Transform.In;
        for (i1 = 0; i1 < nTransforms; i1++) {
            if (i1 == nTransforms - 1) {
                whichTrans = ICC_Transform.Out;
            } else {
                if ((whichTrans == ICC_Transform.Simulation) && (theProfiles[i1].getProfileClass() == ICC_Profile.CLASS_ABSTRACT)) {
                    renderState = ICC_Profile.icPerceptual;
                    whichTrans = ICC_Transform.In;
                }
            }
            theTransforms[i1] = new ICC_Transform(theProfiles[i1], renderState, whichTrans);
            renderState = getRenderingIntent(theProfiles[i1]);
            whichTrans = ICC_Transform.Simulation;
        }
        thisTransform = new ICC_Transform(theTransforms);
        thisSrcProfile = srcProfile;
        thisDestProfile = destProfile;
    }
    
    public final WritableRaster filter(Raster src, WritableRaster dest) {
        if (CSList != null) {
            return nonICCRasterFilter(src, dest);
        }
        int nProfiles = profileList.length;
        if (nProfiles < 2) {
            throw new IllegalArgumentException("Source or Destination ColorSpace is undefined");
        }
        if (src.getNumBands() != profileList[0].getNumComponents()) {
            throw new IllegalArgumentException("Numbers of source Raster bands and source color space components do not match");
        }
        if (dest == null) {
            dest = createCompatibleDestRaster(src);
        } else {
            if (src.getHeight() != dest.getHeight() || src.getWidth() != dest.getWidth()) {
                throw new IllegalArgumentException("Width or height of Rasters do not match");
            }
            if (dest.getNumBands() != profileList[nProfiles - 1].getNumComponents()) {
                throw new IllegalArgumentException("Numbers of destination Raster bands and destination color space components do not match");
            }
        }
        if (thisRasterTransform == null) {
            int i1;
            int whichTrans;
            int renderState;
            ICC_Transform[] theTransforms;
            theTransforms = new ICC_Transform[nProfiles];
            if (profileList[0].getProfileClass() == ICC_Profile.CLASS_OUTPUT) {
                renderState = ICC_Profile.icRelativeColorimetric;
            } else {
                renderState = ICC_Profile.icPerceptual;
            }
            whichTrans = ICC_Transform.In;
            for (i1 = 0; i1 < nProfiles; i1++) {
                if (i1 == nProfiles - 1) {
                    whichTrans = ICC_Transform.Out;
                } else {
                    if ((whichTrans == ICC_Transform.Simulation) && (profileList[i1].getProfileClass() == ICC_Profile.CLASS_ABSTRACT)) {
                        renderState = ICC_Profile.icPerceptual;
                        whichTrans = ICC_Transform.In;
                    }
                }
                theTransforms[i1] = new ICC_Transform(profileList[i1], renderState, whichTrans);
                renderState = getRenderingIntent(profileList[i1]);
                whichTrans = ICC_Transform.Simulation;
            }
            thisRasterTransform = new ICC_Transform(theTransforms);
        }
        int srcTransferType = src.getTransferType();
        int dstTransferType = dest.getTransferType();
        if ((srcTransferType == DataBuffer.TYPE_FLOAT) || (srcTransferType == DataBuffer.TYPE_DOUBLE) || (dstTransferType == DataBuffer.TYPE_FLOAT) || (dstTransferType == DataBuffer.TYPE_DOUBLE)) {
            if (srcMinVals == null) {
                getMinMaxValsFromProfiles(profileList[0], profileList[nProfiles - 1]);
            }
            thisRasterTransform.colorConvert(src, dest, srcMinVals, srcMaxVals, dstMinVals, dstMaxVals);
        } else {
            thisRasterTransform.colorConvert(src, dest);
        }
        return dest;
    }
    
    public final Rectangle2D getBounds2D(BufferedImage src) {
        return getBounds2D(src.getRaster());
    }
    
    public final Rectangle2D getBounds2D(Raster src) {
        return src.getBounds();
    }
    
    public BufferedImage createCompatibleDestImage(BufferedImage src, ColorModel destCM) {
        ColorSpace cs = null;
        ;
        if (destCM == null) {
            if (CSList == null) {
                int nProfiles = profileList.length;
                if (nProfiles == 0) {
                    throw new IllegalArgumentException("Destination ColorSpace is undefined");
                }
                ICC_Profile destProfile = profileList[nProfiles - 1];
                cs = new ICC_ColorSpace(destProfile);
            } else {
                int nSpaces = CSList.length;
                cs = CSList[nSpaces - 1];
            }
        }
        return createCompatibleDestImage(src, destCM, cs);
    }
    
    private BufferedImage createCompatibleDestImage(BufferedImage src, ColorModel destCM, ColorSpace destCS) {
        BufferedImage image;
        if (destCM == null) {
            ColorModel srcCM = src.getColorModel();
            int nbands = destCS.getNumComponents();
            boolean hasAlpha = srcCM.hasAlpha();
            if (hasAlpha) {
                nbands += 1;
            }
            int[] nbits = new int[nbands];
            for (int i = 0; i < nbands; i++) {
                nbits[i] = 8;
            }
            destCM = new ComponentColorModel(destCS, nbits, hasAlpha, srcCM.isAlphaPremultiplied(), srcCM.getTransparency(), DataBuffer.TYPE_BYTE);
        }
        int w = src.getWidth();
        int h = src.getHeight();
        image = new BufferedImage(destCM, destCM.createCompatibleWritableRaster(w, h), destCM.isAlphaPremultiplied(), null);
        return image;
    }
    
    public WritableRaster createCompatibleDestRaster(Raster src) {
        int ncomponents;
        if (CSList != null) {
            if (CSList.length != 2) {
                throw new IllegalArgumentException("Destination ColorSpace is undefined");
            }
            ncomponents = CSList[1].getNumComponents();
        } else {
            int nProfiles = profileList.length;
            if (nProfiles < 2) {
                throw new IllegalArgumentException("Destination ColorSpace is undefined");
            }
            ncomponents = profileList[nProfiles - 1].getNumComponents();
        }
        WritableRaster dest = Raster.createInterleavedRaster(DataBuffer.TYPE_BYTE, src.getWidth(), src.getHeight(), ncomponents, new Point(src.getMinX(), src.getMinY()));
        return dest;
    }
    
    public final Point2D getPoint2D(Point2D srcPt, Point2D dstPt) {
        if (dstPt == null) {
            dstPt = new Point2D$Float();
        }
        dstPt.setLocation(srcPt.getX(), srcPt.getY());
        return dstPt;
    }
    
    private int getRenderingIntent(ICC_Profile profile) {
        byte[] header = profile.getData(ICC_Profile.icSigHead);
        int index = ICC_Profile.icHdrRenderingIntent;
        return (((header[index] & 255) << 24) | ((header[index + 1] & 255) << 16) | ((header[index + 2] & 255) << 8) | (header[index + 3] & 255));
    }
    
    public final RenderingHints getRenderingHints() {
        return hints;
    }
    
    private final BufferedImage nonICCBIFilter(BufferedImage src, ColorSpace srcColorSpace, BufferedImage dst, ColorSpace dstColorSpace) {
        int w = src.getWidth();
        int h = src.getHeight();
        ICC_ColorSpace ciespace = (ICC_ColorSpace)(ICC_ColorSpace)ColorSpace.getInstance(ColorSpace.CS_CIEXYZ);
        if (dst == null) {
            dst = createCompatibleDestImage(src, null);
            dstColorSpace = dst.getColorModel().getColorSpace();
        } else {
            if ((h != dst.getHeight()) || (w != dst.getWidth())) {
                throw new IllegalArgumentException("Width or height of BufferedImages do not match");
            }
        }
        Raster srcRas = src.getRaster();
        WritableRaster dstRas = dst.getRaster();
        ColorModel srcCM = src.getColorModel();
        ColorModel dstCM = dst.getColorModel();
        int srcNumComp = srcCM.getNumColorComponents();
        int dstNumComp = dstCM.getNumColorComponents();
        boolean dstHasAlpha = dstCM.hasAlpha();
        boolean needSrcAlpha = srcCM.hasAlpha() && dstHasAlpha;
        ColorSpace[] list;
        if ((CSList == null) && (profileList.length != 0)) {
            boolean nonICCSrc;
            boolean nonICCDst;
            ICC_Profile srcProfile;
            ICC_Profile dstProfile;
            if (!(srcColorSpace instanceof ICC_ColorSpace)) {
                nonICCSrc = true;
                srcProfile = ciespace.getProfile();
            } else {
                nonICCSrc = false;
                srcProfile = ((ICC_ColorSpace)(ICC_ColorSpace)srcColorSpace).getProfile();
            }
            if (!(dstColorSpace instanceof ICC_ColorSpace)) {
                nonICCDst = true;
                dstProfile = ciespace.getProfile();
            } else {
                nonICCDst = false;
                dstProfile = ((ICC_ColorSpace)(ICC_ColorSpace)dstColorSpace).getProfile();
            }
            if ((thisTransform == null) || (thisSrcProfile != srcProfile) || (thisDestProfile != dstProfile)) {
                updateBITransform(srcProfile, dstProfile);
            }
            float maxNum = 65535.0F;
            ColorSpace cs;
            int iccSrcNumComp;
            if (nonICCSrc) {
                cs = ciespace;
                iccSrcNumComp = 3;
            } else {
                cs = srcColorSpace;
                iccSrcNumComp = srcNumComp;
            }
            float[] srcMinVal = new float[iccSrcNumComp];
            float[] srcInvDiffMinMax = new float[iccSrcNumComp];
            for (int i = 0; i < srcNumComp; i++) {
                srcMinVal[i] = cs.getMinValue(i);
                srcInvDiffMinMax[i] = maxNum / (cs.getMaxValue(i) - srcMinVal[i]);
            }
            int iccDstNumComp;
            if (nonICCDst) {
                cs = ciespace;
                iccDstNumComp = 3;
            } else {
                cs = dstColorSpace;
                iccDstNumComp = dstNumComp;
            }
            float[] dstMinVal = new float[iccDstNumComp];
            float[] dstDiffMinMax = new float[iccDstNumComp];
            for (int i = 0; i < dstNumComp; i++) {
                dstMinVal[i] = cs.getMinValue(i);
                dstDiffMinMax[i] = (cs.getMaxValue(i) - dstMinVal[i]) / maxNum;
            }
            float[] dstColor;
            if (dstHasAlpha) {
                int size = ((dstNumComp + 1) > 3) ? (dstNumComp + 1) : 3;
                dstColor = new float[size];
            } else {
                int size = (dstNumComp > 3) ? dstNumComp : 3;
                dstColor = new float[size];
            }
            short[] srcLine = new short[w * iccSrcNumComp];
            short[] dstLine = new short[w * iccDstNumComp];
            Object pixel;
            float[] color;
            float[] alpha = null;
            if (needSrcAlpha) {
                alpha = new float[w];
            }
            int idx;
            for (int y = 0; y < h; y++) {
                pixel = null;
                color = null;
                idx = 0;
                for (int x = 0; x < w; x++) {
                    pixel = srcRas.getDataElements(x, y, pixel);
                    color = srcCM.getNormalizedComponents(pixel, color, 0);
                    if (needSrcAlpha) {
                        alpha[x] = color[srcNumComp];
                    }
                    if (nonICCSrc) {
                        color = srcColorSpace.toCIEXYZ(color);
                    }
                    for (int i = 0; i < iccSrcNumComp; i++) {
                        srcLine[idx++] = (short)((color[i] - srcMinVal[i]) * srcInvDiffMinMax[i] + 0.5F);
                    }
                }
                thisTransform.colorConvert(srcLine, dstLine);
                pixel = null;
                idx = 0;
                for (int x = 0; x < w; x++) {
                    for (int i = 0; i < iccDstNumComp; i++) {
                        dstColor[i] = ((float)(dstLine[idx++] & 65535)) * dstDiffMinMax[i] + dstMinVal[i];
                    }
                    if (nonICCDst) {
                        color = srcColorSpace.fromCIEXYZ(dstColor);
                        for (int i = 0; i < dstNumComp; i++) {
                            dstColor[i] = color[i];
                        }
                    }
                    if (needSrcAlpha) {
                        dstColor[dstNumComp] = alpha[x];
                    } else if (dstHasAlpha) {
                        dstColor[dstNumComp] = 1.0F;
                    }
                    pixel = dstCM.getDataElements(dstColor, 0, pixel);
                    dstRas.setDataElements(x, y, pixel);
                }
            }
        } else {
            int numCS;
            if (CSList == null) {
                numCS = 0;
            } else {
                numCS = CSList.length;
            }
            float[] dstColor;
            if (dstHasAlpha) {
                dstColor = new float[dstNumComp + 1];
            } else {
                dstColor = new float[dstNumComp];
            }
            Object spixel = null;
            Object dpixel = null;
            float[] color = null;
            float[] tmpColor;
            for (int y = 0; y < h; y++) {
                for (int x = 0; x < w; x++) {
                    spixel = srcRas.getDataElements(x, y, spixel);
                    color = srcCM.getNormalizedComponents(spixel, color, 0);
                    tmpColor = srcColorSpace.toCIEXYZ(color);
                    for (int i = 0; i < numCS; i++) {
                        tmpColor = CSList[i].fromCIEXYZ(tmpColor);
                        tmpColor = CSList[i].toCIEXYZ(tmpColor);
                    }
                    tmpColor = dstColorSpace.fromCIEXYZ(tmpColor);
                    for (int i = 0; i < dstNumComp; i++) {
                        dstColor[i] = tmpColor[i];
                    }
                    if (needSrcAlpha) {
                        dstColor[dstNumComp] = color[srcNumComp];
                    } else if (dstHasAlpha) {
                        dstColor[dstNumComp] = 1.0F;
                    }
                    dpixel = dstCM.getDataElements(dstColor, 0, dpixel);
                    dstRas.setDataElements(x, y, dpixel);
                }
            }
        }
        return dst;
    }
    
    private final WritableRaster nonICCRasterFilter(Raster src, WritableRaster dst) {
        if (CSList.length != 2) {
            throw new IllegalArgumentException("Destination ColorSpace is undefined");
        }
        if (src.getNumBands() != CSList[0].getNumComponents()) {
            throw new IllegalArgumentException("Numbers of source Raster bands and source color space components do not match");
        }
        if (dst == null) {
            dst = createCompatibleDestRaster(src);
        } else {
            if (src.getHeight() != dst.getHeight() || src.getWidth() != dst.getWidth()) {
                throw new IllegalArgumentException("Width or height of Rasters do not match");
            }
            if (dst.getNumBands() != CSList[1].getNumComponents()) {
                throw new IllegalArgumentException("Numbers of destination Raster bands and destination color space components do not match");
            }
        }
        if (srcMinVals == null) {
            getMinMaxValsFromColorSpaces(CSList[0], CSList[1]);
        }
        SampleModel srcSM = src.getSampleModel();
        SampleModel dstSM = dst.getSampleModel();
        boolean srcIsFloat;
        boolean dstIsFloat;
        int srcTransferType = src.getTransferType();
        int dstTransferType = dst.getTransferType();
        if ((srcTransferType == DataBuffer.TYPE_FLOAT) || (srcTransferType == DataBuffer.TYPE_DOUBLE)) {
            srcIsFloat = true;
        } else {
            srcIsFloat = false;
        }
        if ((dstTransferType == DataBuffer.TYPE_FLOAT) || (dstTransferType == DataBuffer.TYPE_DOUBLE)) {
            dstIsFloat = true;
        } else {
            dstIsFloat = false;
        }
        int w = src.getWidth();
        int h = src.getHeight();
        int srcNumBands = src.getNumBands();
        int dstNumBands = dst.getNumBands();
        float[] srcScaleFactor = null;
        float[] dstScaleFactor = null;
        if (!srcIsFloat) {
            srcScaleFactor = new float[srcNumBands];
            for (int i = 0; i < srcNumBands; i++) {
                if (srcTransferType == DataBuffer.TYPE_SHORT) {
                    srcScaleFactor[i] = (srcMaxVals[i] - srcMinVals[i]) / 32767.0F;
                } else {
                    srcScaleFactor[i] = (srcMaxVals[i] - srcMinVals[i]) / ((float)((1 << srcSM.getSampleSize(i)) - 1));
                }
            }
        }
        if (!dstIsFloat) {
            dstScaleFactor = new float[dstNumBands];
            for (int i = 0; i < dstNumBands; i++) {
                if (dstTransferType == DataBuffer.TYPE_SHORT) {
                    dstScaleFactor[i] = 32767.0F / (dstMaxVals[i] - dstMinVals[i]);
                } else {
                    dstScaleFactor[i] = ((float)((1 << dstSM.getSampleSize(i)) - 1)) / (dstMaxVals[i] - dstMinVals[i]);
                }
            }
        }
        int ys = src.getMinY();
        int yd = dst.getMinY();
        int xs;
        int xd;
        float sample;
        float[] color = new float[srcNumBands];
        float[] tmpColor;
        ColorSpace srcColorSpace = CSList[0];
        ColorSpace dstColorSpace = CSList[1];
        for (int y = 0; y < h; y++, ys++, yd++) {
            xs = src.getMinX();
            xd = dst.getMinX();
            for (int x = 0; x < w; x++, xs++, xd++) {
                for (int i = 0; i < srcNumBands; i++) {
                    sample = src.getSampleFloat(xs, ys, i);
                    if (!srcIsFloat) {
                        sample = sample * srcScaleFactor[i] + srcMinVals[i];
                    }
                    color[i] = sample;
                }
                tmpColor = srcColorSpace.toCIEXYZ(color);
                tmpColor = dstColorSpace.fromCIEXYZ(tmpColor);
                for (int i = 0; i < dstNumBands; i++) {
                    sample = tmpColor[i];
                    if (!dstIsFloat) {
                        sample = (sample - dstMinVals[i]) * dstScaleFactor[i];
                    }
                    dst.setSample(xd, yd, i, sample);
                }
            }
        }
        return dst;
    }
    
    private void getMinMaxValsFromProfiles(ICC_Profile srcProfile, ICC_Profile dstProfile) {
        int type = srcProfile.getColorSpaceType();
        int nc = srcProfile.getNumComponents();
        srcMinVals = new float[nc];
        srcMaxVals = new float[nc];
        setMinMax(type, nc, srcMinVals, srcMaxVals);
        type = dstProfile.getColorSpaceType();
        nc = dstProfile.getNumComponents();
        dstMinVals = new float[nc];
        dstMaxVals = new float[nc];
        setMinMax(type, nc, dstMinVals, dstMaxVals);
    }
    
    private void setMinMax(int type, int nc, float[] minVals, float[] maxVals) {
        if (type == ColorSpace.TYPE_Lab) {
            minVals[0] = 0.0F;
            maxVals[0] = 100.0F;
            minVals[1] = -128.0F;
            maxVals[1] = 127.0F;
            minVals[2] = -128.0F;
            maxVals[2] = 127.0F;
        } else if (type == ColorSpace.TYPE_XYZ) {
            minVals[0] = minVals[1] = minVals[2] = 0.0F;
            maxVals[0] = maxVals[1] = maxVals[2] = 1.0F + (32767.0F / 32768.0F);
        } else {
            for (int i = 0; i < nc; i++) {
                minVals[i] = 0.0F;
                maxVals[i] = 1.0F;
            }
        }
    }
    
    private void getMinMaxValsFromColorSpaces(ColorSpace srcCspace, ColorSpace dstCspace) {
        int nc = srcCspace.getNumComponents();
        srcMinVals = new float[nc];
        srcMaxVals = new float[nc];
        for (int i = 0; i < nc; i++) {
            srcMinVals[i] = srcCspace.getMinValue(i);
            srcMaxVals[i] = srcCspace.getMaxValue(i);
        }
        nc = dstCspace.getNumComponents();
        dstMinVals = new float[nc];
        dstMaxVals = new float[nc];
        for (int i = 0; i < nc; i++) {
            dstMinVals[i] = dstCspace.getMinValue(i);
            dstMaxVals[i] = dstCspace.getMaxValue(i);
        }
    }
}
