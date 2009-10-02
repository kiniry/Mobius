package javax.print;

import java.io.IOException;

public interface MultiDoc {
    
    public Doc getDoc() throws IOException;
    
    public MultiDoc next() throws IOException;
}
