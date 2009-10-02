package java.net;

import java.io.IOException;

class UnknownContentHandler extends ContentHandler {
    
    UnknownContentHandler() {
        
    }
    
    public Object getContent(URLConnection uc) throws IOException {
        return uc.getInputStream();
    }
}
