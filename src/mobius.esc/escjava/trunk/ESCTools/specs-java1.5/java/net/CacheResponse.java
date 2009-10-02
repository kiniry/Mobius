package java.net;

import java.io.InputStream;
import java.util.Map;
import java.io.IOException;

public abstract class CacheResponse {
    
    public CacheResponse() {
        
    }
    
    public abstract Map getHeaders() throws IOException;
    
    public abstract InputStream getBody() throws IOException;
}
