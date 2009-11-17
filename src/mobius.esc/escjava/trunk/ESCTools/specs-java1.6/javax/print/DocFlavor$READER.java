package javax.print;

public class DocFlavor$READER extends DocFlavor {
    private static final long serialVersionUID = 7100295812579351567L;
    
    public DocFlavor$READER(String mimeType) {
        super(mimeType, "java.io.Reader");
    }
    public static final DocFlavor$READER TEXT_PLAIN = new DocFlavor$READER("text/plain; charset=utf-16");
    public static final DocFlavor$READER TEXT_HTML = new DocFlavor$READER("text/html; charset=utf-16");
}
