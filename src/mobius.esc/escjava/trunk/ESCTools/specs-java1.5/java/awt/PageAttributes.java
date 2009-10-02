package java.awt;

import java.util.Locale;

public final class PageAttributes implements Cloneable {
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    private PageAttributes$ColorType color;
    private PageAttributes$MediaType media;
    private PageAttributes$OrientationRequestedType orientationRequested;
    private PageAttributes$OriginType origin;
    private PageAttributes$PrintQualityType printQuality;
    private int[] printerResolution;
    
    public PageAttributes() {
        
        setColor(PageAttributes$ColorType.MONOCHROME);
        setMediaToDefault();
        setOrientationRequestedToDefault();
        setOrigin(PageAttributes$OriginType.PHYSICAL);
        setPrintQualityToDefault();
        setPrinterResolutionToDefault();
    }
    
    public PageAttributes(PageAttributes obj) {
        
        set(obj);
    }
    
    public PageAttributes(PageAttributes$ColorType color, PageAttributes$MediaType media, PageAttributes$OrientationRequestedType orientationRequested, PageAttributes$OriginType origin, PageAttributes$PrintQualityType printQuality, int[] printerResolution) {
        
        setColor(color);
        setMedia(media);
        setOrientationRequested(orientationRequested);
        setOrigin(origin);
        setPrintQuality(printQuality);
        setPrinterResolution(printerResolution);
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public void set(PageAttributes obj) {
        color = obj.color;
        media = obj.media;
        orientationRequested = obj.orientationRequested;
        origin = obj.origin;
        printQuality = obj.printQuality;
        printerResolution = obj.printerResolution;
    }
    
    public PageAttributes$ColorType getColor() {
        return color;
    }
    
    public void setColor(PageAttributes$ColorType color) {
        if (color == null) {
            throw new IllegalArgumentException("Invalid value for attribute color");
        }
        this.color = color;
    }
    
    public PageAttributes$MediaType getMedia() {
        return media;
    }
    
    public void setMedia(PageAttributes$MediaType media) {
        if (media == null) {
            throw new IllegalArgumentException("Invalid value for attribute media");
        }
        this.media = media;
    }
    
    public void setMediaToDefault() {
        String defaultCountry = Locale.getDefault().getCountry();
        if (defaultCountry != null && (defaultCountry.equals(Locale.US.getCountry()) || defaultCountry.equals(Locale.CANADA.getCountry()))) {
            setMedia(PageAttributes$MediaType.NA_LETTER);
        } else {
            setMedia(PageAttributes$MediaType.ISO_A4);
        }
    }
    
    public PageAttributes$OrientationRequestedType getOrientationRequested() {
        return orientationRequested;
    }
    
    public void setOrientationRequested(PageAttributes$OrientationRequestedType orientationRequested) {
        if (orientationRequested == null) {
            throw new IllegalArgumentException("Invalid value for attribute orientationRequested");
        }
        this.orientationRequested = orientationRequested;
    }
    
    public void setOrientationRequested(int orientationRequested) {
        switch (orientationRequested) {
        case 3: 
            setOrientationRequested(PageAttributes$OrientationRequestedType.PORTRAIT);
            break;
        
        case 4: 
            setOrientationRequested(PageAttributes$OrientationRequestedType.LANDSCAPE);
            break;
        
        default: 
            setOrientationRequested(null);
            break;
        
        }
    }
    
    public void setOrientationRequestedToDefault() {
        setOrientationRequested(PageAttributes$OrientationRequestedType.PORTRAIT);
    }
    
    public PageAttributes$OriginType getOrigin() {
        return origin;
    }
    
    public void setOrigin(PageAttributes$OriginType origin) {
        if (origin == null) {
            throw new IllegalArgumentException("Invalid value for attribute origin");
        }
        this.origin = origin;
    }
    
    public PageAttributes$PrintQualityType getPrintQuality() {
        return printQuality;
    }
    
    public void setPrintQuality(PageAttributes$PrintQualityType printQuality) {
        if (printQuality == null) {
            throw new IllegalArgumentException("Invalid value for attribute printQuality");
        }
        this.printQuality = printQuality;
    }
    
    public void setPrintQuality(int printQuality) {
        switch (printQuality) {
        case 3: 
            setPrintQuality(PageAttributes$PrintQualityType.DRAFT);
            break;
        
        case 4: 
            setPrintQuality(PageAttributes$PrintQualityType.NORMAL);
            break;
        
        case 5: 
            setPrintQuality(PageAttributes$PrintQualityType.HIGH);
            break;
        
        default: 
            setPrintQuality(null);
            break;
        
        }
    }
    
    public void setPrintQualityToDefault() {
        setPrintQuality(PageAttributes$PrintQualityType.NORMAL);
    }
    
    public int[] getPrinterResolution() {
        int[] copy = new int[3];
        copy[0] = printerResolution[0];
        copy[1] = printerResolution[1];
        copy[2] = printerResolution[2];
        return copy;
    }
    
    public void setPrinterResolution(int[] printerResolution) {
        if (printerResolution == null || printerResolution.length != 3 || printerResolution[0] <= 0 || printerResolution[1] <= 0 || (printerResolution[2] != 3 && printerResolution[2] != 4)) {
            throw new IllegalArgumentException("Invalid value for attribute printerResolution");
        }
        int[] copy = new int[3];
        copy[0] = printerResolution[0];
        copy[1] = printerResolution[1];
        copy[2] = printerResolution[2];
        this.printerResolution = copy;
    }
    
    public void setPrinterResolution(int printerResolution) {
        setPrinterResolution(new int[]{printerResolution, printerResolution, 3});
    }
    
    public void setPrinterResolutionToDefault() {
        setPrinterResolution(72);
    }
    
    public boolean equals(Object obj) {
        if (!(obj instanceof PageAttributes)) {
            return false;
        }
        PageAttributes rhs = (PageAttributes)(PageAttributes)obj;
        return (color == rhs.color && media == rhs.media && orientationRequested == rhs.orientationRequested && origin == rhs.origin && printQuality == rhs.printQuality && printerResolution[0] == rhs.printerResolution[0] && printerResolution[1] == rhs.printerResolution[1] && printerResolution[2] == rhs.printerResolution[2]);
    }
    
    public int hashCode() {
        return (color.hashCode() << 31 ^ media.hashCode() << 24 ^ orientationRequested.hashCode() << 23 ^ origin.hashCode() << 22 ^ printQuality.hashCode() << 20 ^ printerResolution[2] >> 2 << 19 ^ printerResolution[1] << 10 ^ printerResolution[0]);
    }
    
    public String toString() {
        return "color=" + getColor() + ",media=" + getMedia() + ",orientation-requested=" + getOrientationRequested() + ",origin=" + getOrigin() + ",print-quality=" + getPrintQuality() + ",printer-resolution=[" + printerResolution[0] + "," + printerResolution[1] + "," + printerResolution[2] + "]";
    }
}
