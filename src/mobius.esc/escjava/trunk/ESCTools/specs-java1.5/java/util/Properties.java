package java.util;

import java.io.IOException;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.BufferedWriter;

public class Properties extends Hashtable {
    private static final long serialVersionUID = 4112578634029874840L;
    protected Properties defaults;
    
    public Properties() {
        this(null);
    }
    
    public Properties(Properties defaults) {
        
        this.defaults = defaults;
    }
    
    public synchronized Object setProperty(String key, String value) {
        return put(key, value);
    }
    
    public synchronized void load(InputStream inStream) throws IOException {
        char[] convtBuf = new char[1024];
        Properties$LineReader lr = new Properties$LineReader(this, inStream);
        int limit;
        int keyLen;
        int valueStart;
        char c;
        boolean hasSep;
        boolean precedingBackslash;
        while ((limit = lr.readLine()) >= 0) {
            c = 0;
            keyLen = 0;
            valueStart = limit;
            hasSep = false;
            precedingBackslash = false;
            while (keyLen < limit) {
                c = lr.lineBuf[keyLen];
                if ((c == '=' || c == ':') && !precedingBackslash) {
                    valueStart = keyLen + 1;
                    hasSep = true;
                    break;
                } else if ((c == ' ' || c == '\t' || c == '\f') && !precedingBackslash) {
                    valueStart = keyLen + 1;
                    break;
                }
                if (c == '\\') {
                    precedingBackslash = !precedingBackslash;
                } else {
                    precedingBackslash = false;
                }
                keyLen++;
            }
            while (valueStart < limit) {
                c = lr.lineBuf[valueStart];
                if (c != ' ' && c != '\t' && c != '\f') {
                    if (!hasSep && (c == '=' || c == ':')) {
                        hasSep = true;
                    } else {
                        break;
                    }
                }
                valueStart++;
            }
            String key = loadConvert(lr.lineBuf, 0, keyLen, convtBuf);
            String value = loadConvert(lr.lineBuf, valueStart, limit - valueStart, convtBuf);
            put(key, value);
        }
    }
    {
    }
    
    private String loadConvert(char[] in, int off, int len, char[] convtBuf) {
        if (convtBuf.length < len) {
            int newLen = len * 2;
            if (newLen < 0) {
                newLen = Integer.MAX_VALUE;
            }
            convtBuf = new char[newLen];
        }
        char aChar;
        char[] out = convtBuf;
        int outLen = 0;
        int end = off + len;
        while (off < end) {
            aChar = in[off++];
            if (aChar == '\\') {
                aChar = in[off++];
                if (aChar == 'u') {
                    int value = 0;
                    for (int i = 0; i < 4; i++) {
                        aChar = in[off++];
                        switch (aChar) {
                        case '0': 
                        
                        case '1': 
                        
                        case '2': 
                        
                        case '3': 
                        
                        case '4': 
                        
                        case '5': 
                        
                        case '6': 
                        
                        case '7': 
                        
                        case '8': 
                        
                        case '9': 
                            value = (value << 4) + aChar - '0';
                            break;
                        
                        case 'a': 
                        
                        case 'b': 
                        
                        case 'c': 
                        
                        case 'd': 
                        
                        case 'e': 
                        
                        case 'f': 
                            value = (value << 4) + 10 + aChar - 'a';
                            break;
                        
                        case 'A': 
                        
                        case 'B': 
                        
                        case 'C': 
                        
                        case 'D': 
                        
                        case 'E': 
                        
                        case 'F': 
                            value = (value << 4) + 10 + aChar - 'A';
                            break;
                        
                        default: 
                            throw new IllegalArgumentException("Malformed \\uxxxx encoding.");
                        
                        }
                    }
                    out[outLen++] = (char)value;
                } else {
                    if (aChar == 't') aChar = '\t'; else if (aChar == 'r') aChar = '\r'; else if (aChar == 'n') aChar = '\n'; else if (aChar == 'f') aChar = '\f';
                    out[outLen++] = aChar;
                }
            } else {
                out[outLen++] = (char)aChar;
            }
        }
        return new String(out, 0, outLen);
    }
    
    private String saveConvert(String theString, boolean escapeSpace) {
        int len = theString.length();
        int bufLen = len * 2;
        if (bufLen < 0) {
            bufLen = Integer.MAX_VALUE;
        }
        StringBuffer outBuffer = new StringBuffer(bufLen);
        for (int x = 0; x < len; x++) {
            char aChar = theString.charAt(x);
            if ((aChar > 61) && (aChar < 127)) {
                if (aChar == '\\') {
                    outBuffer.append('\\');
                    outBuffer.append('\\');
                    continue;
                }
                outBuffer.append(aChar);
                continue;
            }
            switch (aChar) {
            case ' ': 
                if (x == 0 || escapeSpace) outBuffer.append('\\');
                outBuffer.append(' ');
                break;
            
            case '\t': 
                outBuffer.append('\\');
                outBuffer.append('t');
                break;
            
            case '\n': 
                outBuffer.append('\\');
                outBuffer.append('n');
                break;
            
            case '\r': 
                outBuffer.append('\\');
                outBuffer.append('r');
                break;
            
            case '\f': 
                outBuffer.append('\\');
                outBuffer.append('f');
                break;
            
            case '=': 
            
            case ':': 
            
            case '#': 
            
            case '!': 
                outBuffer.append('\\');
                outBuffer.append(aChar);
                break;
            
            default: 
                if ((aChar < 32) || (aChar > 126)) {
                    outBuffer.append('\\');
                    outBuffer.append('u');
                    outBuffer.append(toHex((aChar >> 12) & 15));
                    outBuffer.append(toHex((aChar >> 8) & 15));
                    outBuffer.append(toHex((aChar >> 4) & 15));
                    outBuffer.append(toHex(aChar & 15));
                } else {
                    outBuffer.append(aChar);
                }
            
            }
        }
        return outBuffer.toString();
    }
    
    
    public synchronized void save(OutputStream out, String comments) {
        try {
            store(out, comments);
        } catch (IOException e) {
        }
    }
    
    public synchronized void store(OutputStream out, String comments) throws IOException {
        BufferedWriter awriter;
        awriter = new BufferedWriter(new OutputStreamWriter(out, "8859_1"));
        if (comments != null) writeln(awriter, "#" + comments);
        writeln(awriter, "#" + new Date().toString());
        for (Enumeration e = keys(); e.hasMoreElements(); ) {
            String key = (String)(String)e.nextElement();
            String val = (String)(String)get(key);
            key = saveConvert(key, true);
            val = saveConvert(val, false);
            writeln(awriter, key + "=" + val);
        }
        awriter.flush();
    }
    
    private static void writeln(BufferedWriter bw, String s) throws IOException {
        bw.write(s);
        bw.newLine();
    }
    
    public synchronized void loadFromXML(InputStream in) throws IOException, InvalidPropertiesFormatException {
        if (in == null) throw new NullPointerException();
        XMLUtils.load(this, in);
    }
    
    public synchronized void storeToXML(OutputStream os, String comment) throws IOException {
        if (os == null) throw new NullPointerException();
        storeToXML(os, comment, "UTF-8");
    }
    
    public synchronized void storeToXML(OutputStream os, String comment, String encoding) throws IOException {
        if (os == null) throw new NullPointerException();
        XMLUtils.save(this, os, comment, encoding);
    }
    
    public String getProperty(String key) {
        Object oval = super.get(key);
        String sval = (oval instanceof String) ? (String)(String)oval : null;
        return ((sval == null) && (defaults != null)) ? defaults.getProperty(key) : sval;
    }
    
    public String getProperty(String key, String defaultValue) {
        String val = getProperty(key);
        return (val == null) ? defaultValue : val;
    }
    
    public Enumeration propertyNames() {
        Hashtable h = new Hashtable();
        enumerate(h);
        return h.keys();
    }
    
    public void list(PrintStream out) {
        out.println("-- listing properties --");
        Hashtable h = new Hashtable();
        enumerate(h);
        for (Enumeration e = h.keys(); e.hasMoreElements(); ) {
            String key = (String)(String)e.nextElement();
            String val = (String)(String)h.get(key);
            if (val.length() > 40) {
                val = val.substring(0, 37) + "...";
            }
            out.println(key + "=" + val);
        }
    }
    
    public void list(PrintWriter out) {
        out.println("-- listing properties --");
        Hashtable h = new Hashtable();
        enumerate(h);
        for (Enumeration e = h.keys(); e.hasMoreElements(); ) {
            String key = (String)(String)e.nextElement();
            String val = (String)(String)h.get(key);
            if (val.length() > 40) {
                val = val.substring(0, 37) + "...";
            }
            out.println(key + "=" + val);
        }
    }
    
    private synchronized void enumerate(Hashtable h) {
        if (defaults != null) {
            defaults.enumerate(h);
        }
        for (Enumeration e = keys(); e.hasMoreElements(); ) {
            String key = (String)(String)e.nextElement();
            h.put(key, get(key));
        }
    }
    
    private static char toHex(int nibble) {
        return hexDigit[(nibble & 15)];
    }
    private static final char[] hexDigit = {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'};
}
