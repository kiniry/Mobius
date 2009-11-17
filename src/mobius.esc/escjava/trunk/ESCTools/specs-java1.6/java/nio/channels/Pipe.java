package java.nio.channels;

import java.io.IOException;
import java.nio.channels.spi.*;

public abstract class Pipe {
    {
    }
    {
    }
    
    protected Pipe() {
        
    }
    
    public abstract Pipe$SourceChannel source();
    
    public abstract Pipe$SinkChannel sink();
    
    public static Pipe open() throws IOException {
        return SelectorProvider.provider().openPipe();
    }
}
