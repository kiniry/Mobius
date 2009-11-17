package java.io;

import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;
import sun.nio.cs.StreamDecoder;

public class InputStreamReader extends Reader {
    private final StreamDecoder sd;
    
    public InputStreamReader(InputStream in) {
        super(in);
        try {
            sd = StreamDecoder.forInputStreamReader(in, this, (String)null);
        } catch (UnsupportedEncodingException e) {
            throw new Error(e);
        }
    }
    
    public InputStreamReader(InputStream in, String charsetName) throws UnsupportedEncodingException {
        super(in);
        if (charsetName == null) throw new NullPointerException("charsetName");
        sd = StreamDecoder.forInputStreamReader(in, this, charsetName);
    }
    
    public InputStreamReader(InputStream in, Charset cs) {
        super(in);
        if (cs == null) throw new NullPointerException("charset");
        sd = StreamDecoder.forInputStreamReader(in, this, cs);
    }
    
    public InputStreamReader(InputStream in, CharsetDecoder dec) {
        super(in);
        if (dec == null) throw new NullPointerException("charset decoder");
        sd = StreamDecoder.forInputStreamReader(in, this, dec);
    }
    
    public String getEncoding() {
        return sd.getEncoding();
    }
    
    public int read() throws IOException {
        return sd.read();
    }
    
    public int read(char[] cbuf, int offset, int length) throws IOException {
        return sd.read(cbuf, offset, length);
    }
    
    public boolean ready() throws IOException {
        return sd.ready();
    }
    
    public void close() throws IOException {
        sd.close();
    }
}
