package javax.print;

public class DocFlavor$INPUT_STREAM extends DocFlavor {
    private static final long serialVersionUID = -7045842700749194127L;
    
    public DocFlavor$INPUT_STREAM(String mimeType) {
        super(mimeType, "java.io.InputStream");
    }
    public static final DocFlavor$INPUT_STREAM TEXT_PLAIN_HOST = new DocFlavor$INPUT_STREAM("text/plain; charset=" + hostEncoding);
    public static final DocFlavor$INPUT_STREAM TEXT_PLAIN_UTF_8 = new DocFlavor$INPUT_STREAM("text/plain; charset=utf-8");
    public static final DocFlavor$INPUT_STREAM TEXT_PLAIN_UTF_16 = new DocFlavor$INPUT_STREAM("text/plain; charset=utf-16");
    public static final DocFlavor$INPUT_STREAM TEXT_PLAIN_UTF_16BE = new DocFlavor$INPUT_STREAM("text/plain; charset=utf-16be");
    public static final DocFlavor$INPUT_STREAM TEXT_PLAIN_UTF_16LE = new DocFlavor$INPUT_STREAM("text/plain; charset=utf-16le");
    public static final DocFlavor$INPUT_STREAM TEXT_PLAIN_US_ASCII = new DocFlavor$INPUT_STREAM("text/plain; charset=us-ascii");
    public static final DocFlavor$INPUT_STREAM TEXT_HTML_HOST = new DocFlavor$INPUT_STREAM("text/html; charset=" + hostEncoding);
    public static final DocFlavor$INPUT_STREAM TEXT_HTML_UTF_8 = new DocFlavor$INPUT_STREAM("text/html; charset=utf-8");
    public static final DocFlavor$INPUT_STREAM TEXT_HTML_UTF_16 = new DocFlavor$INPUT_STREAM("text/html; charset=utf-16");
    public static final DocFlavor$INPUT_STREAM TEXT_HTML_UTF_16BE = new DocFlavor$INPUT_STREAM("text/html; charset=utf-16be");
    public static final DocFlavor$INPUT_STREAM TEXT_HTML_UTF_16LE = new DocFlavor$INPUT_STREAM("text/html; charset=utf-16le");
    public static final DocFlavor$INPUT_STREAM TEXT_HTML_US_ASCII = new DocFlavor$INPUT_STREAM("text/html; charset=us-ascii");
    public static final DocFlavor$INPUT_STREAM PDF = new DocFlavor$INPUT_STREAM("application/pdf");
    public static final DocFlavor$INPUT_STREAM POSTSCRIPT = new DocFlavor$INPUT_STREAM("application/postscript");
    public static final DocFlavor$INPUT_STREAM PCL = new DocFlavor$INPUT_STREAM("application/vnd.hp-PCL");
    public static final DocFlavor$INPUT_STREAM GIF = new DocFlavor$INPUT_STREAM("image/gif");
    public static final DocFlavor$INPUT_STREAM JPEG = new DocFlavor$INPUT_STREAM("image/jpeg");
    public static final DocFlavor$INPUT_STREAM PNG = new DocFlavor$INPUT_STREAM("image/png");
    public static final DocFlavor$INPUT_STREAM AUTOSENSE = new DocFlavor$INPUT_STREAM("application/octet-stream");
}
