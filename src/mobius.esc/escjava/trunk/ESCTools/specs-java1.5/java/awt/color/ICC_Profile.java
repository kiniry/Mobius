package java.awt.color;

import sun.awt.color.CMM;
import sun.awt.color.ProfileDeferralMgr;
import sun.awt.color.ProfileDeferralInfo;
import sun.awt.color.ProfileActivator;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamException;
import java.io.OutputStream;
import java.io.Serializable;
import java.util.StringTokenizer;
import java.security.AccessController;

public class ICC_Profile implements Serializable {
    
    /*synthetic*/ static FileInputStream access$000(String x0) {
        return privilegedOpenProfile(x0);
    }
    private static final long serialVersionUID = -3938515861990936766L;
    transient long ID;
    private transient ProfileDeferralInfo deferralInfo;
    private transient ProfileActivator profileActivator;
    private static ICC_Profile sRGBprofile;
    private static ICC_Profile XYZprofile;
    private static ICC_Profile PYCCprofile;
    private static ICC_Profile GRAYprofile;
    private static ICC_Profile LINEAR_RGBprofile;
    public static final int CLASS_INPUT = 0;
    public static final int CLASS_DISPLAY = 1;
    public static final int CLASS_OUTPUT = 2;
    public static final int CLASS_DEVICELINK = 3;
    public static final int CLASS_COLORSPACECONVERSION = 4;
    public static final int CLASS_ABSTRACT = 5;
    public static final int CLASS_NAMEDCOLOR = 6;
    public static final int icSigXYZData = 1482250784;
    public static final int icSigLabData = 1281450528;
    public static final int icSigLuvData = 1282766368;
    public static final int icSigYCbCrData = 1497588338;
    public static final int icSigYxyData = 1501067552;
    public static final int icSigRgbData = 1380401696;
    public static final int icSigGrayData = 1196573017;
    public static final int icSigHsvData = 1213421088;
    public static final int icSigHlsData = 1212961568;
    public static final int icSigCmykData = 1129142603;
    public static final int icSigCmyData = 1129142560;
    public static final int icSigSpace2CLR = 843271250;
    public static final int icSigSpace3CLR = 860048466;
    public static final int icSigSpace4CLR = 876825682;
    public static final int icSigSpace5CLR = 893602898;
    public static final int icSigSpace6CLR = 910380114;
    public static final int icSigSpace7CLR = 927157330;
    public static final int icSigSpace8CLR = 943934546;
    public static final int icSigSpace9CLR = 960711762;
    public static final int icSigSpaceACLR = 1094929490;
    public static final int icSigSpaceBCLR = 1111706706;
    public static final int icSigSpaceCCLR = 1128483922;
    public static final int icSigSpaceDCLR = 1145261138;
    public static final int icSigSpaceECLR = 1162038354;
    public static final int icSigSpaceFCLR = 1178815570;
    public static final int icSigInputClass = 1935896178;
    public static final int icSigDisplayClass = 1835955314;
    public static final int icSigOutputClass = 1886549106;
    public static final int icSigLinkClass = 1818848875;
    public static final int icSigAbstractClass = 1633842036;
    public static final int icSigColorSpaceClass = 1936744803;
    public static final int icSigNamedColorClass = 1852662636;
    public static final int icPerceptual = 0;
    public static final int icRelativeColorimetric = 1;
    public static final int icMediaRelativeColorimetric = 1;
    public static final int icSaturation = 2;
    public static final int icAbsoluteColorimetric = 3;
    public static final int icICCAbsoluteColorimetric = 3;
    public static final int icSigHead = 1751474532;
    public static final int icSigAToB0Tag = 1093812784;
    public static final int icSigAToB1Tag = 1093812785;
    public static final int icSigAToB2Tag = 1093812786;
    public static final int icSigBlueColorantTag = 1649957210;
    public static final int icSigBlueMatrixColumnTag = 1649957210;
    public static final int icSigBlueTRCTag = 1649693251;
    public static final int icSigBToA0Tag = 1110589744;
    public static final int icSigBToA1Tag = 1110589745;
    public static final int icSigBToA2Tag = 1110589746;
    public static final int icSigCalibrationDateTimeTag = 1667329140;
    public static final int icSigCharTargetTag = 1952543335;
    public static final int icSigCopyrightTag = 1668313716;
    public static final int icSigCrdInfoTag = 1668441193;
    public static final int icSigDeviceMfgDescTag = 1684893284;
    public static final int icSigDeviceModelDescTag = 1684890724;
    public static final int icSigDeviceSettingsTag = 1684371059;
    public static final int icSigGamutTag = 1734438260;
    public static final int icSigGrayTRCTag = 1800688195;
    public static final int icSigGreenColorantTag = 1733843290;
    public static final int icSigGreenMatrixColumnTag = 1733843290;
    public static final int icSigGreenTRCTag = 1733579331;
    public static final int icSigLuminanceTag = 1819635049;
    public static final int icSigMeasurementTag = 1835360627;
    public static final int icSigMediaBlackPointTag = 1651208308;
    public static final int icSigMediaWhitePointTag = 2004119668;
    public static final int icSigNamedColor2Tag = 1852009522;
    public static final int icSigOutputResponseTag = 1919251312;
    public static final int icSigPreview0Tag = 1886545200;
    public static final int icSigPreview1Tag = 1886545201;
    public static final int icSigPreview2Tag = 1886545202;
    public static final int icSigProfileDescriptionTag = 1684370275;
    public static final int icSigProfileSequenceDescTag = 1886610801;
    public static final int icSigPs2CRD0Tag = 1886610480;
    public static final int icSigPs2CRD1Tag = 1886610481;
    public static final int icSigPs2CRD2Tag = 1886610482;
    public static final int icSigPs2CRD3Tag = 1886610483;
    public static final int icSigPs2CSATag = 1886597747;
    public static final int icSigPs2RenderingIntentTag = 1886597737;
    public static final int icSigRedColorantTag = 1918392666;
    public static final int icSigRedMatrixColumnTag = 1918392666;
    public static final int icSigRedTRCTag = 1918128707;
    public static final int icSigScreeningDescTag = 1935897188;
    public static final int icSigScreeningTag = 1935897198;
    public static final int icSigTechnologyTag = 1952801640;
    public static final int icSigUcrBgTag = 1650877472;
    public static final int icSigViewingCondDescTag = 1987405156;
    public static final int icSigViewingConditionsTag = 1986618743;
    public static final int icSigChromaticityTag = 1667789421;
    public static final int icSigChromaticAdaptationTag = 1667785060;
    public static final int icSigColorantOrderTag = 1668051567;
    public static final int icSigColorantTableTag = 1668051572;
    public static final int icHdrSize = 0;
    public static final int icHdrCmmId = 4;
    public static final int icHdrVersion = 8;
    public static final int icHdrDeviceClass = 12;
    public static final int icHdrColorSpace = 16;
    public static final int icHdrPcs = 20;
    public static final int icHdrDate = 24;
    public static final int icHdrMagic = 36;
    public static final int icHdrPlatform = 40;
    public static final int icHdrFlags = 44;
    public static final int icHdrManufacturer = 48;
    public static final int icHdrModel = 52;
    public static final int icHdrAttributes = 56;
    public static final int icHdrRenderingIntent = 64;
    public static final int icHdrIlluminant = 68;
    public static final int icHdrCreator = 80;
    public static final int icHdrProfileID = 84;
    public static final int icTagType = 0;
    public static final int icTagReserved = 4;
    public static final int icCurveCount = 8;
    public static final int icCurveData = 12;
    public static final int icXYZNumberX = 8;
    
    ICC_Profile(long ID) {
        
        this.ID = ID;
    }
    
    ICC_Profile(ProfileDeferralInfo pdi) {
        
        this.deferralInfo = pdi;
        this.profileActivator = new ICC_Profile$1(this);
        ProfileDeferralMgr.registerDeferral(this.profileActivator);
    }
    
    protected void finalize() {
        if (ID != 0) {
            CMM.checkStatus(CMM.cmmFreeProfile(ID));
        } else if (profileActivator != null) {
            ProfileDeferralMgr.unregisterDeferral(profileActivator);
        }
    }
    
    public static ICC_Profile getInstance(byte[] data) {
        ICC_Profile thisProfile;
        long[] theID = new long[1];
        if (ProfileDeferralMgr.deferring) {
            ProfileDeferralMgr.activateProfiles();
        }
        try {
            CMM.checkStatus(CMM.cmmLoadProfile(data, theID));
        } catch (CMMException c) {
            throw new IllegalArgumentException("Invalid ICC Profile Data");
        }
        try {
            if ((getColorSpaceType(theID[0]) == ColorSpace.TYPE_GRAY) && (getData(theID[0], icSigMediaWhitePointTag) != null) && (getData(theID[0], icSigGrayTRCTag) != null)) {
                thisProfile = new ICC_ProfileGray(theID[0]);
            } else if ((getColorSpaceType(theID[0]) == ColorSpace.TYPE_RGB) && (getData(theID[0], icSigMediaWhitePointTag) != null) && (getData(theID[0], icSigRedColorantTag) != null) && (getData(theID[0], icSigGreenColorantTag) != null) && (getData(theID[0], icSigBlueColorantTag) != null) && (getData(theID[0], icSigRedTRCTag) != null) && (getData(theID[0], icSigGreenTRCTag) != null) && (getData(theID[0], icSigBlueTRCTag) != null)) {
                thisProfile = new ICC_ProfileRGB(theID[0]);
            } else {
                thisProfile = new ICC_Profile(theID[0]);
            }
        } catch (CMMException c) {
            thisProfile = new ICC_Profile(theID[0]);
        }
        return thisProfile;
    }
    
    public static ICC_Profile getInstance(int cspace) {
        ICC_Profile thisProfile = null;
        String fileName;
        switch (cspace) {
        case ColorSpace.CS_sRGB: 
            synchronized (ICC_Profile.class) {
                if (sRGBprofile == null) {
                    try {
                        sRGBprofile = getDeferredInstance(new ProfileDeferralInfo("sRGB.pf", ColorSpace.TYPE_RGB, 3, CLASS_DISPLAY));
                    } catch (IOException e) {
                        throw new IllegalArgumentException("Can\'t load standard profile: sRGB.pf");
                    }
                }
                thisProfile = sRGBprofile;
            }
            break;
        
        case ColorSpace.CS_CIEXYZ: 
            synchronized (ICC_Profile.class) {
                if (XYZprofile == null) {
                    XYZprofile = getStandardProfile("CIEXYZ.pf");
                }
                thisProfile = XYZprofile;
            }
            break;
        
        case ColorSpace.CS_PYCC: 
            synchronized (ICC_Profile.class) {
                if (PYCCprofile == null) {
                    PYCCprofile = getStandardProfile("PYCC.pf");
                }
                thisProfile = PYCCprofile;
            }
            break;
        
        case ColorSpace.CS_GRAY: 
            synchronized (ICC_Profile.class) {
                if (GRAYprofile == null) {
                    GRAYprofile = getStandardProfile("GRAY.pf");
                }
                thisProfile = GRAYprofile;
            }
            break;
        
        case ColorSpace.CS_LINEAR_RGB: 
            synchronized (ICC_Profile.class) {
                if (LINEAR_RGBprofile == null) {
                    LINEAR_RGBprofile = getStandardProfile("LINEAR_RGB.pf");
                }
                thisProfile = LINEAR_RGBprofile;
            }
            break;
        
        default: 
            throw new IllegalArgumentException("Unknown color space");
        
        }
        return thisProfile;
    }
    
    private static ICC_Profile getStandardProfile(final String name) {
        return (ICC_Profile)(ICC_Profile)AccessController.doPrivileged(new ICC_Profile$2(name));
    }
    
    public static ICC_Profile getInstance(String fileName) throws IOException {
        ICC_Profile thisProfile;
        FileInputStream fis;
        SecurityManager security = System.getSecurityManager();
        if (security != null) {
            security.checkRead(fileName);
        }
        if ((fis = openProfile(fileName)) == null) {
            throw new IOException("Cannot open file " + fileName);
        }
        thisProfile = getInstance(fis);
        fis.close();
        return thisProfile;
    }
    
    public static ICC_Profile getInstance(InputStream s) throws IOException {
        byte[] profileData;
        if (s instanceof ProfileDeferralInfo) {
            return getDeferredInstance((ProfileDeferralInfo)(ProfileDeferralInfo)s);
        }
        if ((profileData = getProfileDataFromStream(s)) == null) {
            throw new IllegalArgumentException("Invalid ICC Profile Data");
        }
        return getInstance(profileData);
    }
    
    static byte[] getProfileDataFromStream(InputStream s) throws IOException {
        byte[] profileData;
        int profileSize;
        byte[] header = new byte[128];
        int bytestoread = 128;
        int bytesread = 0;
        int n;
        while (bytestoread != 0) {
            if ((n = s.read(header, bytesread, bytestoread)) < 0) {
                return null;
            }
            bytesread += n;
            bytestoread -= n;
        }
        if (header[36] != 97 || header[37] != 99 || header[38] != 115 || header[39] != 112) {
            return null;
        }
        profileSize = ((header[0] & 255) << 24) | ((header[1] & 255) << 16) | ((header[2] & 255) << 8) | (header[3] & 255);
        profileData = new byte[profileSize];
        System.arraycopy(header, 0, profileData, 0, 128);
        bytestoread = profileSize - 128;
        bytesread = 128;
        while (bytestoread != 0) {
            if ((n = s.read(profileData, bytesread, bytestoread)) < 0) {
                return null;
            }
            bytesread += n;
            bytestoread -= n;
        }
        return profileData;
    }
    
    static ICC_Profile getDeferredInstance(ProfileDeferralInfo pdi) throws IOException {
        if (!ProfileDeferralMgr.deferring) {
            return getStandardProfile(pdi.filename);
        }
        if (pdi.colorSpaceType == ColorSpace.TYPE_RGB) {
            return new ICC_ProfileRGB(pdi);
        } else if (pdi.colorSpaceType == ColorSpace.TYPE_GRAY) {
            return new ICC_ProfileGray(pdi);
        } else {
            return new ICC_Profile(pdi);
        }
    }
    
    void activateDeferredProfile() {
        long[] theID = new long[1];
        byte[] profileData;
        FileInputStream fis;
        String fileName = deferralInfo.filename;
        profileActivator = null;
        deferralInfo = null;
        if ((fis = openProfile(fileName)) == null) {
            throw new IllegalArgumentException("Cannot open file " + fileName);
        }
        try {
            profileData = getProfileDataFromStream(fis);
            fis.close();
        } catch (IOException e) {
            throw new IllegalArgumentException("Invalid ICC Profile Data" + fileName);
        }
        if (profileData == null) {
            throw new IllegalArgumentException("Invalid ICC Profile Data" + fileName);
        }
        try {
            CMM.checkStatus(CMM.cmmLoadProfile(profileData, theID));
        } catch (CMMException c) {
            throw new IllegalArgumentException("Invalid ICC Profile Data" + fileName);
        }
        ID = theID[0];
    }
    
    public int getMajorVersion() {
        byte[] theHeader;
        theHeader = getData(icSigHead);
        return (int)theHeader[8];
    }
    
    public int getMinorVersion() {
        byte[] theHeader;
        theHeader = getData(icSigHead);
        return (int)theHeader[9];
    }
    
    public int getProfileClass() {
        byte[] theHeader;
        int theClassSig;
        int theClass;
        if (deferralInfo != null) {
            return deferralInfo.profileClass;
        }
        theHeader = getData(icSigHead);
        theClassSig = intFromBigEndian(theHeader, icHdrDeviceClass);
        switch (theClassSig) {
        case icSigInputClass: 
            theClass = CLASS_INPUT;
            break;
        
        case icSigDisplayClass: 
            theClass = CLASS_DISPLAY;
            break;
        
        case icSigOutputClass: 
            theClass = CLASS_OUTPUT;
            break;
        
        case icSigLinkClass: 
            theClass = CLASS_DEVICELINK;
            break;
        
        case icSigColorSpaceClass: 
            theClass = CLASS_COLORSPACECONVERSION;
            break;
        
        case icSigAbstractClass: 
            theClass = CLASS_ABSTRACT;
            break;
        
        case icSigNamedColorClass: 
            theClass = CLASS_NAMEDCOLOR;
            break;
        
        default: 
            throw new IllegalArgumentException("Unknown profile class");
        
        }
        return theClass;
    }
    
    public int getColorSpaceType() {
        if (deferralInfo != null) {
            return deferralInfo.colorSpaceType;
        }
        return getColorSpaceType(ID);
    }
    
    static int getColorSpaceType(long profileID) {
        byte[] theHeader;
        int theColorSpaceSig;
        int theColorSpace;
        theHeader = getData(profileID, icSigHead);
        theColorSpaceSig = intFromBigEndian(theHeader, icHdrColorSpace);
        theColorSpace = iccCStoJCS(theColorSpaceSig);
        return theColorSpace;
    }
    
    public int getPCSType() {
        if (ProfileDeferralMgr.deferring) {
            ProfileDeferralMgr.activateProfiles();
        }
        return getPCSType(ID);
    }
    
    static int getPCSType(long profileID) {
        byte[] theHeader;
        int thePCSSig;
        int thePCS;
        theHeader = getData(profileID, icSigHead);
        thePCSSig = intFromBigEndian(theHeader, icHdrPcs);
        thePCS = iccCStoJCS(thePCSSig);
        return thePCS;
    }
    
    public void write(String fileName) throws IOException {
        FileOutputStream outputFile;
        byte[] profileData;
        profileData = getData();
        outputFile = new FileOutputStream(fileName);
        outputFile.write(profileData);
        outputFile.close();
    }
    
    public void write(OutputStream s) throws IOException {
        byte[] profileData;
        profileData = getData();
        s.write(profileData);
    }
    
    public byte[] getData() {
        int[] profileSize = new int[1];
        byte[] profileData;
        if (ProfileDeferralMgr.deferring) {
            ProfileDeferralMgr.activateProfiles();
        }
        CMM.checkStatus(CMM.cmmGetProfileSize(ID, profileSize));
        profileData = new byte[profileSize[0]];
        CMM.checkStatus(CMM.cmmGetProfileData(ID, profileData));
        return profileData;
    }
    
    public byte[] getData(int tagSignature) {
        if (ProfileDeferralMgr.deferring) {
            ProfileDeferralMgr.activateProfiles();
        }
        return getData(ID, tagSignature);
    }
    
    static byte[] getData(long profileID, int tagSignature) {
        int[] tagSize = new int[1];
        byte[] tagData;
        try {
            CMM.checkStatus(CMM.cmmGetTagSize(profileID, tagSignature, tagSize));
            tagData = new byte[tagSize[0]];
            CMM.checkStatus(CMM.cmmGetTagData(profileID, tagSignature, tagData));
        } catch (CMMException c) {
            tagData = null;
        }
        return tagData;
    }
    
    public void setData(int tagSignature, byte[] tagData) {
        if (ProfileDeferralMgr.deferring) {
            ProfileDeferralMgr.activateProfiles();
        }
        CMM.checkStatus(CMM.cmmSetTagData(ID, tagSignature, tagData));
    }
    
    void setRenderingIntent(int renderingIntent) {
        byte[] theHeader = getData(icSigHead);
        intToBigEndian(renderingIntent, theHeader, icHdrRenderingIntent);
        setData(icSigHead, theHeader);
    }
    
    int getRenderingIntent() {
        byte[] theHeader = getData(icSigHead);
        int renderingIntent = intFromBigEndian(theHeader, icHdrRenderingIntent);
        return renderingIntent;
    }
    
    public int getNumComponents() {
        byte[] theHeader;
        int theColorSpaceSig;
        int theNumComponents;
        if (deferralInfo != null) {
            return deferralInfo.numComponents;
        }
        theHeader = getData(icSigHead);
        theColorSpaceSig = intFromBigEndian(theHeader, icHdrColorSpace);
        switch (theColorSpaceSig) {
        case icSigGrayData: 
            theNumComponents = 1;
            break;
        
        case icSigSpace2CLR: 
            theNumComponents = 2;
            break;
        
        case icSigXYZData: 
        
        case icSigLabData: 
        
        case icSigLuvData: 
        
        case icSigYCbCrData: 
        
        case icSigYxyData: 
        
        case icSigRgbData: 
        
        case icSigHsvData: 
        
        case icSigHlsData: 
        
        case icSigCmyData: 
        
        case icSigSpace3CLR: 
            theNumComponents = 3;
            break;
        
        case icSigCmykData: 
        
        case icSigSpace4CLR: 
            theNumComponents = 4;
            break;
        
        case icSigSpace5CLR: 
            theNumComponents = 5;
            break;
        
        case icSigSpace6CLR: 
            theNumComponents = 6;
            break;
        
        case icSigSpace7CLR: 
            theNumComponents = 7;
            break;
        
        case icSigSpace8CLR: 
            theNumComponents = 8;
            break;
        
        case icSigSpace9CLR: 
            theNumComponents = 9;
            break;
        
        case icSigSpaceACLR: 
            theNumComponents = 10;
            break;
        
        case icSigSpaceBCLR: 
            theNumComponents = 11;
            break;
        
        case icSigSpaceCCLR: 
            theNumComponents = 12;
            break;
        
        case icSigSpaceDCLR: 
            theNumComponents = 13;
            break;
        
        case icSigSpaceECLR: 
            theNumComponents = 14;
            break;
        
        case icSigSpaceFCLR: 
            theNumComponents = 15;
            break;
        
        default: 
            throw new ProfileDataException("invalid ICC color space");
        
        }
        return theNumComponents;
    }
    
    float[] getMediaWhitePoint() {
        return getXYZTag(icSigMediaWhitePointTag);
    }
    
    float[] getXYZTag(int theTagSignature) {
        byte[] theData;
        float[] theXYZNumber;
        int i1;
        int i2;
        int theS15Fixed16;
        theData = getData(theTagSignature);
        theXYZNumber = new float[3];
        for (i1 = 0, i2 = icXYZNumberX; i1 < 3; i1++, i2 += 4) {
            theS15Fixed16 = intFromBigEndian(theData, i2);
            theXYZNumber[i1] = ((float)theS15Fixed16) / 65536.0F;
        }
        return theXYZNumber;
    }
    
    float getGamma(int theTagSignature) {
        byte[] theTRCData;
        float theGamma;
        int theU8Fixed8;
        theTRCData = getData(theTagSignature);
        if (intFromBigEndian(theTRCData, icCurveCount) != 1) {
            throw new ProfileDataException("TRC is not a gamma");
        }
        theU8Fixed8 = (shortFromBigEndian(theTRCData, icCurveData)) & 65535;
        theGamma = ((float)theU8Fixed8) / 256.0F;
        return theGamma;
    }
    
    short[] getTRC(int theTagSignature) {
        byte[] theTRCData;
        short[] theTRC;
        int i1;
        int i2;
        int nElements;
        int theU8Fixed8;
        theTRCData = getData(theTagSignature);
        nElements = intFromBigEndian(theTRCData, icCurveCount);
        if (nElements == 1) {
            throw new ProfileDataException("TRC is not a table");
        }
        theTRC = new short[nElements];
        for (i1 = 0, i2 = icCurveData; i1 < nElements; i1++, i2 += 2) {
            theTRC[i1] = shortFromBigEndian(theTRCData, i2);
        }
        return theTRC;
    }
    
    static int iccCStoJCS(int theColorSpaceSig) {
        int theColorSpace;
        switch (theColorSpaceSig) {
        case icSigXYZData: 
            theColorSpace = ColorSpace.TYPE_XYZ;
            break;
        
        case icSigLabData: 
            theColorSpace = ColorSpace.TYPE_Lab;
            break;
        
        case icSigLuvData: 
            theColorSpace = ColorSpace.TYPE_Luv;
            break;
        
        case icSigYCbCrData: 
            theColorSpace = ColorSpace.TYPE_YCbCr;
            break;
        
        case icSigYxyData: 
            theColorSpace = ColorSpace.TYPE_Yxy;
            break;
        
        case icSigRgbData: 
            theColorSpace = ColorSpace.TYPE_RGB;
            break;
        
        case icSigGrayData: 
            theColorSpace = ColorSpace.TYPE_GRAY;
            break;
        
        case icSigHsvData: 
            theColorSpace = ColorSpace.TYPE_HSV;
            break;
        
        case icSigHlsData: 
            theColorSpace = ColorSpace.TYPE_HLS;
            break;
        
        case icSigCmykData: 
            theColorSpace = ColorSpace.TYPE_CMYK;
            break;
        
        case icSigCmyData: 
            theColorSpace = ColorSpace.TYPE_CMY;
            break;
        
        case icSigSpace2CLR: 
            theColorSpace = ColorSpace.TYPE_2CLR;
            break;
        
        case icSigSpace3CLR: 
            theColorSpace = ColorSpace.TYPE_3CLR;
            break;
        
        case icSigSpace4CLR: 
            theColorSpace = ColorSpace.TYPE_4CLR;
            break;
        
        case icSigSpace5CLR: 
            theColorSpace = ColorSpace.TYPE_5CLR;
            break;
        
        case icSigSpace6CLR: 
            theColorSpace = ColorSpace.TYPE_6CLR;
            break;
        
        case icSigSpace7CLR: 
            theColorSpace = ColorSpace.TYPE_7CLR;
            break;
        
        case icSigSpace8CLR: 
            theColorSpace = ColorSpace.TYPE_8CLR;
            break;
        
        case icSigSpace9CLR: 
            theColorSpace = ColorSpace.TYPE_9CLR;
            break;
        
        case icSigSpaceACLR: 
            theColorSpace = ColorSpace.TYPE_ACLR;
            break;
        
        case icSigSpaceBCLR: 
            theColorSpace = ColorSpace.TYPE_BCLR;
            break;
        
        case icSigSpaceCCLR: 
            theColorSpace = ColorSpace.TYPE_CCLR;
            break;
        
        case icSigSpaceDCLR: 
            theColorSpace = ColorSpace.TYPE_DCLR;
            break;
        
        case icSigSpaceECLR: 
            theColorSpace = ColorSpace.TYPE_ECLR;
            break;
        
        case icSigSpaceFCLR: 
            theColorSpace = ColorSpace.TYPE_FCLR;
            break;
        
        default: 
            throw new IllegalArgumentException("Unknown color space");
        
        }
        return theColorSpace;
    }
    
    static int intFromBigEndian(byte[] array, int index) {
        return (((array[index] & 255) << 24) | ((array[index + 1] & 255) << 16) | ((array[index + 2] & 255) << 8) | (array[index + 3] & 255));
    }
    
    static void intToBigEndian(int value, byte[] array, int index) {
        array[index] = (byte)(value >> 24);
        array[index + 1] = (byte)(value >> 16);
        array[index + 2] = (byte)(value >> 8);
        array[index + 3] = (byte)(value);
    }
    
    static short shortFromBigEndian(byte[] array, int index) {
        return (short)(((array[index] & 255) << 8) | (array[index + 1] & 255));
    }
    
    static void shortToBigEndian(short value, byte[] array, int index) {
        array[index] = (byte)(value >> 8);
        array[index + 1] = (byte)(value);
    }
    
    private static FileInputStream openProfile(final String fileName) {
        return (FileInputStream)(FileInputStream)java.security.AccessController.doPrivileged(new ICC_Profile$3(fileName));
    }
    
    private static FileInputStream privilegedOpenProfile(String fileName) {
        FileInputStream fis = null;
        String path;
        String dir;
        String fullPath;
        File f = new File(fileName);
        if ((!f.isFile()) && ((path = System.getProperty("java.iccprofile.path")) != null)) {
            StringTokenizer st = new StringTokenizer(path, File.pathSeparator);
            while (st.hasMoreTokens() && (!f.isFile())) {
                dir = st.nextToken();
                fullPath = dir + File.separatorChar + fileName;
                f = new File(fullPath);
            }
        }
        if ((!f.isFile()) && ((path = System.getProperty("java.class.path")) != null)) {
            StringTokenizer st = new StringTokenizer(path, File.pathSeparator);
            while (st.hasMoreTokens() && (!f.isFile())) {
                dir = st.nextToken();
                fullPath = dir + File.separatorChar + fileName;
                f = new File(fullPath);
            }
        }
        if (!f.isFile()) {
            dir = System.getProperty("java.home") + File.separatorChar + "lib" + File.separatorChar + "cmm";
            fullPath = dir + File.separatorChar + fileName;
            f = new File(fullPath);
        }
        if (f.isFile()) {
            try {
                fis = new FileInputStream(f);
            } catch (FileNotFoundException e) {
            }
        }
        return fis;
    }
    private int iccProfileSerializedDataVersion = 1;
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        String csName = null;
        if (this == sRGBprofile) {
            csName = "CS_sRGB";
        } else if (this == XYZprofile) {
            csName = "CS_CIEXYZ";
        } else if (this == PYCCprofile) {
            csName = "CS_PYCC";
        } else if (this == GRAYprofile) {
            csName = "CS_GRAY";
        } else if (this == LINEAR_RGBprofile) {
            csName = "CS_LINEAR_RGB";
        }
        byte[] data = null;
        if (csName == null) {
            data = getData();
        }
        s.writeObject(csName);
        s.writeObject(data);
    }
    private transient ICC_Profile resolvedDeserializedProfile;
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        String csName = (String)(String)s.readObject();
        byte[] data = (byte[])(byte[])s.readObject();
        int cspace = 0;
        boolean isKnownPredefinedCS = false;
        if (csName != null) {
            isKnownPredefinedCS = true;
            if (csName.equals("CS_sRGB")) {
                cspace = ColorSpace.CS_sRGB;
            } else if (csName.equals("CS_CIEXYZ")) {
                cspace = ColorSpace.CS_CIEXYZ;
            } else if (csName.equals("CS_PYCC")) {
                cspace = ColorSpace.CS_PYCC;
            } else if (csName.equals("CS_GRAY")) {
                cspace = ColorSpace.CS_GRAY;
            } else if (csName.equals("CS_LINEAR_RGB")) {
                cspace = ColorSpace.CS_LINEAR_RGB;
            } else {
                isKnownPredefinedCS = false;
            }
        }
        if (isKnownPredefinedCS) {
            resolvedDeserializedProfile = getInstance(cspace);
        } else {
            resolvedDeserializedProfile = getInstance(data);
        }
    }
    
    protected Object readResolve() throws ObjectStreamException {
        return resolvedDeserializedProfile;
    }
}
