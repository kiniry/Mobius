package java.util;

import java.io.*;
import java.security.AccessController;
import java.text.MessageFormat;
import sun.security.action.GetPropertyAction;
import sun.text.resources.LocaleData;

public final class Locale implements Cloneable, Serializable {
    public static final Locale ENGLISH = new Locale("en", "", "");
    public static final Locale FRENCH = new Locale("fr", "", "");
    public static final Locale GERMAN = new Locale("de", "", "");
    public static final Locale ITALIAN = new Locale("it", "", "");
    public static final Locale JAPANESE = new Locale("ja", "", "");
    public static final Locale KOREAN = new Locale("ko", "", "");
    public static final Locale CHINESE = new Locale("zh", "", "");
    public static final Locale SIMPLIFIED_CHINESE = new Locale("zh", "CN", "");
    public static final Locale TRADITIONAL_CHINESE = new Locale("zh", "TW", "");
    public static final Locale FRANCE = new Locale("fr", "FR", "");
    public static final Locale GERMANY = new Locale("de", "DE", "");
    public static final Locale ITALY = new Locale("it", "IT", "");
    public static final Locale JAPAN = new Locale("ja", "JP", "");
    public static final Locale KOREA = new Locale("ko", "KR", "");
    public static final Locale CHINA = new Locale("zh", "CN", "");
    public static final Locale PRC = new Locale("zh", "CN", "");
    public static final Locale TAIWAN = new Locale("zh", "TW", "");
    public static final Locale UK = new Locale("en", "GB", "");
    public static final Locale US = new Locale("en", "US", "");
    public static final Locale CANADA = new Locale("en", "CA", "");
    public static final Locale CANADA_FRENCH = new Locale("fr", "CA", "");
    static final long serialVersionUID = 9149081749638150636L;
    
    public Locale(String language, String country, String variant) {
        
        this.language = convertOldISOCodes(language);
        this.country = toUpperCase(country).intern();
        this.variant = variant.intern();
    }
    
    public Locale(String language, String country) {
        this(language, country, "");
    }
    
    public Locale(String language) {
        this(language, "", "");
    }
    
    public static Locale getDefault() {
        if (defaultLocale == null) {
            String language;
            String region;
            String country;
            String variant;
            language = (String)(String)AccessController.doPrivileged(new GetPropertyAction("user.language", "en"));
            region = (String)(String)AccessController.doPrivileged(new GetPropertyAction("user.region"));
            if (region != null) {
                int i = region.indexOf('_');
                if (i >= 0) {
                    country = region.substring(0, i);
                    variant = region.substring(i + 1);
                } else {
                    country = region;
                    variant = "";
                }
            } else {
                country = (String)(String)AccessController.doPrivileged(new GetPropertyAction("user.country", ""));
                variant = (String)(String)AccessController.doPrivileged(new GetPropertyAction("user.variant", ""));
            }
            defaultLocale = new Locale(language, country, variant);
        }
        return defaultLocale;
    }
    
    public static synchronized void setDefault(Locale newLocale) {
        if (newLocale == null) throw new NullPointerException("Can\'t set default locale to NULL");
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(new PropertyPermission("user.language", "write"));
        defaultLocale = newLocale;
    }
    
    public static Locale[] getAvailableLocales() {
        return LocaleData.getAvailableLocales("LocaleString");
    }
    
    public static String[] getISOCountries() {
        if (isoCountries == null) {
            isoCountries = new String[compressedIsoCountries.length() / 6];
            for (int i = 0; i < isoCountries.length; i++) isoCountries[i] = compressedIsoCountries.substring((i * 6) + 1, (i * 6) + 3);
        }
        String[] result = new String[isoCountries.length];
        System.arraycopy(isoCountries, 0, result, 0, isoCountries.length);
        return result;
    }
    
    public static String[] getISOLanguages() {
        if (isoLanguages == null) {
            isoLanguages = new String[compressedIsoLanguages.length() / 6];
            for (int i = 0; i < isoLanguages.length; i++) isoLanguages[i] = compressedIsoLanguages.substring((i * 6) + 1, (i * 6) + 3);
        }
        String[] result = new String[isoLanguages.length];
        System.arraycopy(isoLanguages, 0, result, 0, isoLanguages.length);
        return result;
    }
    
    public String getLanguage() {
        return language;
    }
    
    public String getCountry() {
        return country;
    }
    
    public String getVariant() {
        return variant;
    }
    
    public final String toString() {
        boolean l = language.length() != 0;
        boolean c = country.length() != 0;
        boolean v = variant.length() != 0;
        StringBuffer result = new StringBuffer(language);
        if (c || (l && v)) {
            result.append('_').append(country);
        }
        if (v && (l || c)) {
            result.append('_').append(variant);
        }
        return result.toString();
    }
    
    public String getISO3Language() throws MissingResourceException {
        int length = language.length();
        if (length == 0) {
            return "";
        }
        int index = compressedIsoLanguages.indexOf("," + language);
        if (index == -1 || length != 2) {
            throw new MissingResourceException("Couldn\'t find 3-letter language code for " + language, "LocaleElements_" + toString(), "ShortLanguage");
        }
        return compressedIsoLanguages.substring(index + 3, index + 6);
    }
    
    public String getISO3Country() throws MissingResourceException {
        int length = country.length();
        if (length == 0) {
            return "";
        }
        int index = compressedIsoCountries.indexOf("," + country);
        if (index == -1 || length != 2) {
            throw new MissingResourceException("Couldn\'t find 3-letter country code for " + country, "LocaleElements_" + toString(), "ShortCountry");
        }
        return compressedIsoCountries.substring(index + 3, index + 6);
    }
    
    public final String getDisplayLanguage() {
        return getDisplayLanguage(getDefault());
    }
    
    public String getDisplayLanguage(Locale inLocale) {
        String langCode = language;
        if (langCode.length() == 0) return "";
        Locale workingLocale = (Locale)(Locale)inLocale.clone();
        String result = null;
        int phase = 0;
        boolean done = false;
        if (workingLocale.variant.length() == 0) phase = 1;
        if (workingLocale.country.length() == 0) phase = 2;
        while (!done) {
            try {
                ResourceBundle bundle = LocaleData.getLocaleElements(workingLocale);
                result = findStringMatch((String[][])(String[][])bundle.getObject("Languages"), langCode, langCode);
                if (result.length() != 0) done = true;
            } catch (Exception e) {
            }
            if (!done) {
                switch (phase) {
                case 0: 
                    workingLocale = new Locale(workingLocale.language, workingLocale.country, "");
                    break;
                
                case 1: 
                    workingLocale = new Locale(workingLocale.language, "", workingLocale.variant);
                    break;
                
                case 2: 
                    workingLocale = getDefault();
                    break;
                
                case 3: 
                    workingLocale = new Locale("", "", "");
                    break;
                
                default: 
                    return langCode;
                
                }
                phase++;
            }
        }
        return result;
    }
    
    public final String getDisplayCountry() {
        return getDisplayCountry(getDefault());
    }
    
    public String getDisplayCountry(Locale inLocale) {
        String ctryCode = country;
        if (ctryCode.length() == 0) return "";
        Locale workingLocale = (Locale)(Locale)inLocale.clone();
        String result = null;
        int phase = 0;
        boolean done = false;
        if (workingLocale.variant.length() == 0) phase = 1;
        if (workingLocale.country.length() == 0) phase = 2;
        while (!done) {
            try {
                ResourceBundle bundle = LocaleData.getLocaleElements(workingLocale);
                result = findStringMatch((String[][])(String[][])bundle.getObject("Countries"), ctryCode, ctryCode);
                if (result.length() != 0) done = true;
            } catch (Exception e) {
            }
            if (!done) {
                switch (phase) {
                case 0: 
                    workingLocale = new Locale(workingLocale.language, workingLocale.country, "");
                    break;
                
                case 1: 
                    workingLocale = new Locale(workingLocale.language, "", workingLocale.variant);
                    break;
                
                case 2: 
                    workingLocale = getDefault();
                    break;
                
                case 3: 
                    workingLocale = new Locale("", "", "");
                    break;
                
                default: 
                    return ctryCode;
                
                }
                phase++;
            }
        }
        return result;
    }
    
    public final String getDisplayVariant() {
        return getDisplayVariant(getDefault());
    }
    
    public String getDisplayVariant(Locale inLocale) {
        if (variant.length() == 0) return "";
        ResourceBundle bundle = LocaleData.getLocaleElements(inLocale);
        String[] names = getDisplayVariantArray(bundle);
        String[] patterns;
        try {
            patterns = (String[])(String[])bundle.getObject("LocaleNamePatterns");
        } catch (MissingResourceException e) {
            patterns = null;
        }
        return formatList(patterns, names);
    }
    
    public final String getDisplayName() {
        return getDisplayName(getDefault());
    }
    
    public String getDisplayName(Locale inLocale) {
        ResourceBundle bundle = LocaleData.getLocaleElements(inLocale);
        String languageName = getDisplayLanguage(inLocale);
        String countryName = getDisplayCountry(inLocale);
        String[] variantNames = getDisplayVariantArray(bundle);
        String[] patterns;
        try {
            patterns = (String[])(String[])bundle.getObject("LocaleNamePatterns");
        } catch (MissingResourceException e) {
            patterns = null;
        }
        String mainName = null;
        String[] qualifierNames = null;
        if (languageName.length() != 0) {
            mainName = languageName;
            if (countryName.length() != 0) {
                qualifierNames = new String[variantNames.length + 1];
                System.arraycopy(variantNames, 0, qualifierNames, 1, variantNames.length);
                qualifierNames[0] = countryName;
            } else qualifierNames = variantNames;
        } else if (countryName.length() != 0) {
            mainName = countryName;
            qualifierNames = variantNames;
        } else {
            return formatList(patterns, variantNames);
        }
        Object[] displayNames = {new Integer(qualifierNames.length != 0 ? 2 : 1), mainName, qualifierNames.length != 0 ? formatList(patterns, qualifierNames) : null};
        if (patterns != null) {
            return new MessageFormat(patterns[0]).format(displayNames);
        } else {
            StringBuffer result = new StringBuffer();
            result.append((String)(String)displayNames[1]);
            if (displayNames.length > 2) {
                result.append(" (");
                result.append((String)(String)displayNames[2]);
                result.append(")");
            }
            return result.toString();
        }
    }
    
    public Object clone() {
        try {
            Locale that = (Locale)(Locale)super.clone();
            return that;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public int hashCode() {
        int hc = hashCodeValue;
        if (hc == 0) {
            hc = (language.hashCode() << 8) ^ country.hashCode() ^ (variant.hashCode() << 4);
            hashCodeValue = hc;
        }
        return hc;
    }
    
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Locale)) return false;
        Locale other = (Locale)(Locale)obj;
        return language == other.language && country == other.country && variant == other.variant;
    }
    private final String language;
    private final String country;
    private final String variant;
    private volatile int hashcode = -1;
    private volatile transient int hashCodeValue = 0;
    private static Locale defaultLocale = null;
    
    private String[] getDisplayVariantArray(ResourceBundle bundle) {
        StringTokenizer tokenizer = new StringTokenizer(variant, "_");
        String[] names = new String[tokenizer.countTokens()];
        for (int i = 0; i < names.length; ++i) {
            String token = tokenizer.nextToken();
            try {
                names[i] = (String)(String)bundle.getObject("%%" + token);
            } catch (MissingResourceException e) {
                names[i] = token;
            }
        }
        return names;
    }
    
    private static String formatList(String[] patterns, String[] stringList) {
        if (patterns == null) {
            StringBuffer result = new StringBuffer();
            for (int i = 0; i < stringList.length; ++i) {
                if (i > 0) result.append(',');
                result.append(stringList[i]);
            }
            return result.toString();
        }
        if (stringList.length > 3) {
            MessageFormat format = new MessageFormat(patterns[2]);
            stringList = composeList(format, stringList);
        }
        Object[] args = new Object[stringList.length + 1];
        System.arraycopy(stringList, 0, args, 1, stringList.length);
        args[0] = new Integer(stringList.length);
        MessageFormat format = new MessageFormat(patterns[1]);
        return format.format(args);
    }
    
    private static String[] composeList(MessageFormat format, String[] list) {
        if (list.length <= 3) return list;
        String[] listItems = {list[0], list[1]};
        String newItem = format.format(listItems);
        String[] newList = new String[list.length - 1];
        System.arraycopy(list, 2, newList, 1, newList.length - 1);
        newList[0] = newItem;
        return composeList(format, newList);
    }
    
    private Object readResolve() throws java.io.ObjectStreamException {
        return new Locale(language, country, variant);
    }
    private static String[] isoLanguages = null;
    private static final String compressedIsoLanguages = ",aaaar,ababk,aeave,afafr,akaka,amamh,anarg,arara,asasm,avava,ayaym,azaze,babak,bebel,bgbul,bhbih,bibis,bmbam,bnben,bobod,brbre,bsbos,cacat,ceche,chcha,cocos,crcre,csces,cuchu,cvchv,cycym,dadan,dedeu,dvdiv,dzdzo,eeewe,elell,eneng,eoepo,esspa,etest,eueus,fafas,ffful,fifin,fjfij,fofao,frfra,fyfry,gagle,gdgla,glglg,gngrn,guguj,gvglv,hahau,heheb,hihin,hohmo,hrhrv,hthat,huhun,hyhye,hzher,iaina,idind,ieile,igibo,iiiii,ikipk,inind,ioido,isisl,itita,iuiku,iwheb,jajpn,jiyid,jvjav,kakat,kgkon,kikik,kjkua,kkkaz,klkal,kmkhm,knkan,kokor,krkau,kskas,kukur,kvkom,kwcor,kykir,lalat,lbltz,lglug,lilim,lnlin,lolao,ltlit,lulub,lvlav,mgmlg,mhmah,mimri,mkmkd,mlmal,mnmon,momol,mrmar,msmsa,mtmlt,mymya,nanau,nbnob,ndnde,nenep,ngndo,nlnld,nnnno,nonor,nrnbl,nvnav,nynya,ococi,ojoji,omorm,orori,ososs,papan,pipli,plpol,pspus,ptpor,quque,rmroh,rnrun,roron,rurus,rwkin,sasan,scsrd,sdsnd,sesme,sgsag,sisin,skslk,slslv,smsmo,snsna,sosom,sqsqi,srsrp,ssssw,stsot,susun,svswe,swswa,tatam,tetel,tgtgk,ththa,titir,tktuk,tltgl,tntsn,toton,trtur,tstso,tttat,twtwi,tytah,uguig,ukukr,ururd,uzuzb,veven,vivie,vovol,wawln,wowol,xhxho,yiyid,yoyor,zazha,zhzho,zuzul";
    private static String[] isoCountries = null;
    private static final String compressedIsoCountries = ",ADAND,AEARE,AFAFG,AGATG,AIAIA,ALALB,AMARM,ANANT,AOAGO,AQATA,ARARG,ASASM,ATAUT,AUAUS,AWABW,AXALA,AZAZE,BABIH,BBBRB,BDBGD,BEBEL,BFBFA,BGBGR,BHBHR,BIBDI,BJBEN,BMBMU,BNBRN,BOBOL,BRBRA,BSBHS,BTBTN,BVBVT,BWBWA,BYBLR,BZBLZ,CACAN,CCCCK,CDCOD,CFCAF,CGCOG,CHCHE,CICIV,CKCOK,CLCHL,CMCMR,CNCHN,COCOL,CRCRI,CSSCG,CUCUB,CVCPV,CXCXR,CYCYP,CZCZE,DEDEU,DJDJI,DKDNK,DMDMA,DODOM,DZDZA,ECECU,EEEST,EGEGY,EHESH,ERERI,ESESP,ETETH,FIFIN,FJFJI,FKFLK,FMFSM,FOFRO,FRFRA,GAGAB,GBGBR,GDGRD,GEGEO,GFGUF,GHGHA,GIGIB,GLGRL,GMGMB,GNGIN,GPGLP,GQGNQ,GRGRC,GSSGS,GTGTM,GUGUM,GWGNB,GYGUY,HKHKG,HMHMD,HNHND,HRHRV,HTHTI,HUHUN,IDIDN,IEIRL,ILISR,ININD,IOIOT,IQIRQ,IRIRN,ISISL,ITITA,JMJAM,JOJOR,JPJPN,KEKEN,KGKGZ,KHKHM,KIKIR,KMCOM,KNKNA,KPPRK,KRKOR,KWKWT,KYCYM,KZKAZ,LALAO,LBLBN,LCLCA,LILIE,LKLKA,LRLBR,LSLSO,LTLTU,LULUX,LVLVA,LYLBY,MAMAR,MCMCO,MDMDA,MGMDG,MHMHL,MKMKD,MLMLI,MMMMR,MNMNG,MOMAC,MPMNP,MQMTQ,MRMRT,MSMSR,MTMLT,MUMUS,MVMDV,MWMWI,MXMEX,MYMYS,MZMOZ,NANAM,NCNCL,NENER,NFNFK,NGNGA,NINIC,NLNLD,NONOR,NPNPL,NRNRU,NUNIU,NZNZL,OMOMN,PAPAN,PEPER,PFPYF,PGPNG,PHPHL,PKPAK,PLPOL,PMSPM,PNPCN,PRPRI,PSPSE,PTPRT,PWPLW,PYPRY,QAQAT,REREU,ROROU,RURUS,RWRWA,SASAU,SBSLB,SCSYC,SDSDN,SESWE,SGSGP,SHSHN,SISVN,SJSJM,SKSVK,SLSLE,SMSMR,SNSEN,SOSOM,SRSUR,STSTP,SVSLV,SYSYR,SZSWZ,TCTCA,TDTCD,TFATF,TGTGO,THTHA,TJTJK,TKTKL,TLTLS,TMTKM,TNTUN,TOTON,TRTUR,TTTTO,TVTUV,TWTWN,TZTZA,UAUKR,UGUGA,UMUMI,USUSA,UYURY,UZUZB,VAVAT,VCVCT,VEVEN,VGVGB,VIVIR,VNVNM,VUVUT,WFWLF,WSWSM,YEYEM,YTMYT,ZAZAF,ZMZMB,ZWZWE";
    
    private String toLowerCase(String str) {
        char[] buf = new char[str.length()];
        for (int i = 0; i < buf.length; i++) {
            buf[i] = Character.toLowerCase(str.charAt(i));
        }
        return new String(buf);
    }
    
    private String toUpperCase(String str) {
        char[] buf = new char[str.length()];
        for (int i = 0; i < buf.length; i++) {
            buf[i] = Character.toUpperCase(str.charAt(i));
        }
        return new String(buf);
    }
    
    private String findStringMatch(String[][] languages, String desiredLanguage, String fallbackLanguage) {
        for (int i = 0; i < languages.length; ++i) if (desiredLanguage.equals(languages[i][0])) return languages[i][1];
        if (!fallbackLanguage.equals(desiredLanguage)) for (int i = 0; i < languages.length; ++i) if (fallbackLanguage.equals(languages[i][0])) return languages[i][1];
        if (!"EN".equals(desiredLanguage) && "EN".equals(fallbackLanguage)) for (int i = 0; i < languages.length; ++i) if ("EN".equals(languages[i][0])) return languages[i][1];
        return "";
    }
    
    private String convertOldISOCodes(String language) {
        language = toLowerCase(language).intern();
        if (language == "he") {
            return "iw";
        } else if (language == "yi") {
            return "ji";
        } else if (language == "id") {
            return "in";
        } else {
            return language;
        }
    }
}
