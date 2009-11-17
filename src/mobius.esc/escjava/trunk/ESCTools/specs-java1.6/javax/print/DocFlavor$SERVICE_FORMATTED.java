package javax.print;

public class DocFlavor$SERVICE_FORMATTED extends DocFlavor {
    private static final long serialVersionUID = 6181337766266637256L;
    
    public DocFlavor$SERVICE_FORMATTED(String className) {
        super("application/x-java-jvm-local-objectref", className);
    }
    public static final DocFlavor$SERVICE_FORMATTED RENDERABLE_IMAGE = new DocFlavor$SERVICE_FORMATTED("java.awt.image.renderable.RenderableImage");
    public static final DocFlavor$SERVICE_FORMATTED PRINTABLE = new DocFlavor$SERVICE_FORMATTED("java.awt.print.Printable");
    public static final DocFlavor$SERVICE_FORMATTED PAGEABLE = new DocFlavor$SERVICE_FORMATTED("java.awt.print.Pageable");
}
