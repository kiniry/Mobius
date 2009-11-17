package javax.print;

public class DocFlavor$URL extends DocFlavor {
    
    public DocFlavor$URL(String mimeType) {
        super(mimeType, "java.net.URL");
    }
    public static final DocFlavor$URL TEXT_PLAIN_HOST = new DocFlavor$URL("text/plain; charset=" + hostEncoding);
    public static final DocFlavor$URL TEXT_PLAIN_UTF_8 = new DocFlavor$URL("text/plain; charset=utf-8");
    public static final DocFlavor$URL TEXT_PLAIN_UTF_16 = new DocFlavor$URL("text/plain; charset=utf-16");
    public static final DocFlavor$URL TEXT_PLAIN_UTF_16BE = new DocFlavor$URL("text/plain; charset=utf-16be");
    public static final DocFlavor$URL TEXT_PLAIN_UTF_16LE = new DocFlavor$URL("text/plain; charset=utf-16le");
    public static final DocFlavor$URL TEXT_PLAIN_US_ASCII = new DocFlavor$URL("text/plain; charset=us-ascii");
    public static final DocFlavor$URL TEXT_HTML_HOST = new DocFlavor$URL("text/html; charset=" + hostEncoding);
    public static final DocFlavor$URL TEXT_HTML_UTF_8 = new DocFlavor$URL("text/html; charset=utf-8");
    public static final DocFlavor$URL TEXT_HTML_UTF_16 = new DocFlavor$URL("text/html; charset=utf-16");
    public static final DocFlavor$URL TEXT_HTML_UTF_16BE = new DocFlavor$URL("text/html; charset=utf-16be");
    public static final DocFlavor$URL TEXT_HTML_UTF_16LE = new DocFlavor$URL("text/html; charset=utf-16le");
    public static final DocFlavor$URL TEXT_HTML_US_ASCII = new DocFlavor$URL("text/html; charset=us-ascii");
    public static final DocFlavor$URL PDF = new DocFlavor$URL("application/pdf");
    public static final DocFlavor$URL POSTSCRIPT = new DocFlavor$URL("application/postscript");
    public static final DocFlavor$URL PCL = new DocFlavor$URL("application/vnd.hp-PCL");
    public static final DocFlavor$URL GIF = new DocFlavor$URL("image/gif");
    public static final DocFlavor$URL JPEG = new DocFlavor$URL("image/jpeg");
    public static final DocFlavor$URL PNG = new DocFlavor$URL("image/png");
    public static final DocFlavor$URL AUTOSENSE = new DocFlavor$URL("application/octet-stream");
}
