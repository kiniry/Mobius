package java.nio.channels;

import java.io.IOException;

public interface InterruptibleChannel extends Channel {
    
    public void close() throws IOException;
}
