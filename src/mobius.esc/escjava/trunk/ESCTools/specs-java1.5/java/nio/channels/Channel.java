package java.nio.channels;

import java.io.IOException;
import java.io.Closeable;

public interface Channel extends Closeable {
    
    public boolean isOpen();
    
    public void close() throws IOException;
}
