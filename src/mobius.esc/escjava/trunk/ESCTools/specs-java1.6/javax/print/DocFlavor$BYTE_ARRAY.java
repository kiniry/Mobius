package javax.print;

public class DocFlavor$BYTE_ARRAY extends DocFlavor {
    private static final long serialVersionUID = -9065578006593857475L;
    
    public DocFlavor$BYTE_ARRAY(String mimeType) {
        super(mimeType, "[B");
    }
    public static final DocFlavor$BYTE_ARRAY TEXT_PLAIN_HOST = new DocFlavor$BYTE_ARRAY("text/plain; charset=" + hostEncoding);
    public static final DocFlavor$BYTE_ARRAY TEXT_PLAIN_UTF_8 = new DocFlavor$BYTE_ARRAY("text/plain; charset=utf-8");
    public static final DocFlavor$BYTE_ARRAY TEXT_PLAIN_UTF_16 = new DocFlavor$BYTE_ARRAY("text/plain; charset=utf-16");
    public static final DocFlavor$BYTE_ARRAY TEXT_PLAIN_UTF_16BE = new DocFlavor$BYTE_ARRAY("text/plain; charset=utf-16be");
    public static final DocFlavor$BYTE_ARRAY TEXT_PLAIN_UTF_16LE = new DocFlavor$BYTE_ARRAY("text/plain; charset=utf-16le");
    public static final DocFlavor$BYTE_ARRAY TEXT_PLAIN_US_ASCII = new DocFlavor$BYTE_ARRAY("text/plain; charset=us-ascii");
    public static final DocFlavor$BYTE_ARRAY TEXT_HTML_HOST = new DocFlavor$BYTE_ARRAY("text/html; charset=" + hostEncoding);
    public static final DocFlavor$BYTE_ARRAY TEXT_HTML_UTF_8 = new DocFlavor$BYTE_ARRAY("text/html; charset=utf-8");
    public static final DocFlavor$BYTE_ARRAY TEXT_HTML_UTF_16 = new DocFlavor$BYTE_ARRAY("text/html; charset=utf-16");
    public static final DocFlavor$BYTE_ARRAY TEXT_HTML_UTF_16BE = new DocFlavor$BYTE_ARRAY("text/html; charset=utf-16be");
    public static final DocFlavor$BYTE_ARRAY TEXT_HTML_UTF_16LE = new DocFlavor$BYTE_ARRAY("text/html; charset=utf-16le");
    public static final DocFlavor$BYTE_ARRAY TEXT_HTML_US_ASCII = new DocFlavor$BYTE_ARRAY("text/html; charset=us-ascii");
    public static final DocFlavor$BYTE_ARRAY PDF = new DocFlavor$BYTE_ARRAY("application/pdf");
    public static final DocFlavor$BYTE_ARRAY POSTSCRIPT = new DocFlavor$BYTE_ARRAY("application/postscript");
    public static final DocFlavor$BYTE_ARRAY PCL = new DocFlavor$BYTE_ARRAY("application/vnd.hp-PCL");
    public static final DocFlavor$BYTE_ARRAY GIF = new DocFlavor$BYTE_ARRAY("image/gif");
    public static final DocFlavor$BYTE_ARRAY JPEG = new DocFlavor$BYTE_ARRAY("image/jpeg");
    public static final DocFlavor$BYTE_ARRAY PNG = new DocFlavor$BYTE_ARRAY("image/png");
    public static final DocFlavor$BYTE_ARRAY AUTOSENSE = new DocFlavor$BYTE_ARRAY("application/octet-stream");
}
