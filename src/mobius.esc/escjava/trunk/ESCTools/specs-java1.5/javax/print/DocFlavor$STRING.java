package javax.print;

public class DocFlavor$STRING extends DocFlavor {
    private static final long serialVersionUID = 4414407504887034035L;
    
    public DocFlavor$STRING(String mimeType) {
        super(mimeType, "java.lang.String");
    }
    public static final DocFlavor$STRING TEXT_PLAIN = new DocFlavor$STRING("text/plain; charset=utf-16");
    public static final DocFlavor$STRING TEXT_HTML = new DocFlavor$STRING("text/html; charset=utf-16");
}
