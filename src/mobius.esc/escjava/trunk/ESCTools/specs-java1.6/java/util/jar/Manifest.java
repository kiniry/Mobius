package java.util.jar;

import java.io.DataOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.IOException;
import java.util.Map;
import java.util.HashMap;
import java.util.Iterator;

public class Manifest implements Cloneable {
    private Attributes attr = new Attributes();
    private Map entries = new HashMap();
    
    public Manifest() {
        
    }
    
    public Manifest(InputStream is) throws IOException {
        
        read(is);
    }
    
    public Manifest(Manifest man) {
        
        attr.putAll(man.getMainAttributes());
        entries.putAll(man.getEntries());
    }
    
    public Attributes getMainAttributes() {
        return attr;
    }
    
    public Map getEntries() {
        return entries;
    }
    
    public Attributes getAttributes(String name) {
        return (Attributes)(Attributes)getEntries().get(name);
    }
    
    public void clear() {
        attr.clear();
        entries.clear();
    }
    
    public void write(OutputStream out) throws IOException {
        DataOutputStream dos = new DataOutputStream(out);
        attr.writeMain(dos);
        Iterator it = entries.entrySet().iterator();
        while (it.hasNext()) {
            Map$Entry e = (Map$Entry)(Map$Entry)it.next();
            StringBuffer buffer = new StringBuffer("Name: ");
            String value = (String)(String)e.getKey();
            if (value != null) {
                byte[] vb = value.getBytes("UTF8");
                value = new String(vb, 0, 0, vb.length);
            }
            buffer.append(value);
            buffer.append("\r\n");
            make72Safe(buffer);
            dos.writeBytes(buffer.toString());
            ((Attributes)(Attributes)e.getValue()).write(dos);
        }
        dos.flush();
    }
    
    static void make72Safe(StringBuffer line) {
        int length = line.length();
        if (length > 72) {
            int index = 70;
            while (index < length - 2) {
                line.insert(index, "\r\n ");
                index += 72;
                length += 3;
            }
        }
        return;
    }
    
    public void read(InputStream is) throws IOException {
        Manifest$FastInputStream fis = new Manifest$FastInputStream(is);
        byte[] lbuf = new byte[512];
        attr.read(fis, lbuf);
        int ecount = 0;
        int acount = 0;
        int asize = 2;
        int len;
        String name = null;
        boolean skipEmptyLines = true;
        byte[] lastline = null;
        while ((len = fis.readLine(lbuf)) != -1) {
            if (lbuf[--len] != '\n') {
                throw new IOException("manifest line too long");
            }
            if (len > 0 && lbuf[len - 1] == '\r') {
                --len;
            }
            if (len == 0 && skipEmptyLines) {
                continue;
            }
            skipEmptyLines = false;
            if (name == null) {
                name = parseName(lbuf, len);
                if (name == null) {
                    throw new IOException("invalid manifest format");
                }
                if (fis.peek() == ' ') {
                    lastline = new byte[len - 6];
                    System.arraycopy(lbuf, 6, lastline, 0, len - 6);
                    continue;
                }
            } else {
                byte[] buf = new byte[lastline.length + len - 1];
                System.arraycopy(lastline, 0, buf, 0, lastline.length);
                System.arraycopy(lbuf, 1, buf, lastline.length, len - 1);
                if (fis.peek() == ' ') {
                    lastline = buf;
                    continue;
                }
                name = new String(buf, 0, buf.length, "UTF8");
                lastline = null;
            }
            Attributes attr = getAttributes(name);
            if (attr == null) {
                attr = new Attributes(asize);
                entries.put(name, attr);
            }
            attr.read(fis, lbuf);
            ecount++;
            acount += attr.size();
            asize = Math.max(2, acount / ecount);
            name = null;
            skipEmptyLines = true;
        }
    }
    
    private String parseName(byte[] lbuf, int len) {
        if (toLower(lbuf[0]) == 'n' && toLower(lbuf[1]) == 'a' && toLower(lbuf[2]) == 'm' && toLower(lbuf[3]) == 'e' && lbuf[4] == ':' && lbuf[5] == ' ') {
            try {
                return new String(lbuf, 6, len - 6, "UTF8");
            } catch (Exception e) {
            }
        }
        return null;
    }
    
    private int toLower(int c) {
        return (c >= 'A' && c <= 'Z') ? 'a' + (c - 'A') : c;
    }
    
    public boolean equals(Object o) {
        if (o instanceof Manifest) {
            Manifest m = (Manifest)(Manifest)o;
            return attr.equals(m.getMainAttributes()) && entries.equals(m.getEntries());
        } else {
            return false;
        }
    }
    
    public int hashCode() {
        return attr.hashCode() + entries.hashCode();
    }
    
    public Object clone() {
        return new Manifest(this);
    }
    {
    }
}
