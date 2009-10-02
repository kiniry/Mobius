package javax.print;

import java.io.InputStream;
import java.io.IOException;
import java.io.Reader;
import javax.print.attribute.DocAttributeSet;

public interface Doc {
    
    public DocFlavor getDocFlavor();
    
    public Object getPrintData() throws IOException;
    
    public DocAttributeSet getAttributes();
    
    public Reader getReaderForText() throws IOException;
    
    public InputStream getStreamForBytes() throws IOException;
}
