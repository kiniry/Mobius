package javax.print;

public class DocFlavor$CHAR_ARRAY extends DocFlavor {
    private static final long serialVersionUID = -8720590903724405128L;
    
    public DocFlavor$CHAR_ARRAY(String mimeType) {
        super(mimeType, "[C");
    }
    public static final DocFlavor$CHAR_ARRAY TEXT_PLAIN = new DocFlavor$CHAR_ARRAY("text/plain; charset=utf-16");
    public static final DocFlavor$CHAR_ARRAY TEXT_HTML = new DocFlavor$CHAR_ARRAY("text/html; charset=utf-16");
}
