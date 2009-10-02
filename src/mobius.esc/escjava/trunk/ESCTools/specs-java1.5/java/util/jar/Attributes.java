package java.util.jar;

import java.io.DataOutputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Collection;
import java.util.Iterator;
import java.util.logging.Logger;

public class Attributes implements Map, Cloneable {
    protected Map map;
    
    public Attributes() {
        this(11);
    }
    
    public Attributes(int size) {
        
        map = new HashMap(size);
    }
    
    public Attributes(Attributes attr) {
        
        map = new HashMap(attr);
    }
    
    public Object get(Object name) {
        return map.get(name);
    }
    
    public String getValue(String name) {
        return (String)(String)get(new Attributes$Name((String)name));
    }
    
    public String getValue(Attributes$Name name) {
        return (String)(String)get(name);
    }
    
    public Object put(Object name, Object value) {
        return map.put((Attributes$Name)(Attributes$Name)name, (String)(String)value);
    }
    
    public String putValue(String name, String value) {
        return (String)(String)put(new Attributes$Name(name), value);
    }
    
    public Object remove(Object name) {
        return map.remove(name);
    }
    
    public boolean containsValue(Object value) {
        return map.containsValue(value);
    }
    
    public boolean containsKey(Object name) {
        return map.containsKey(name);
    }
    
    public void putAll(Map attr) {
        if (!Attributes.class.isInstance(attr)) throw new ClassCastException();
        for (Iterator i$ = (attr).entrySet().iterator(); i$.hasNext(); ) {
            Map$Entry me = (Map$Entry)i$.next();
            put(me.getKey(), me.getValue());
        }
    }
    
    public void clear() {
        map.clear();
    }
    
    public int size() {
        return map.size();
    }
    
    public boolean isEmpty() {
        return map.isEmpty();
    }
    
    public Set keySet() {
        return map.keySet();
    }
    
    public Collection values() {
        return map.values();
    }
    
    public Set entrySet() {
        return map.entrySet();
    }
    
    public boolean equals(Object o) {
        return map.equals(o);
    }
    
    public int hashCode() {
        return map.hashCode();
    }
    
    public Object clone() {
        return new Attributes(this);
    }
    
    void write(DataOutputStream os) throws IOException {
        Iterator it = entrySet().iterator();
        while (it.hasNext()) {
            Map$Entry e = (Map$Entry)(Map$Entry)it.next();
            StringBuffer buffer = new StringBuffer(((Attributes$Name)(Attributes$Name)e.getKey()).toString());
            buffer.append(": ");
            String value = (String)(String)e.getValue();
            if (value != null) {
                byte[] vb = value.getBytes("UTF8");
                value = new String(vb, 0, 0, vb.length);
            }
            buffer.append(value);
            buffer.append("\r\n");
            Manifest.make72Safe(buffer);
            os.writeBytes(buffer.toString());
        }
        os.writeBytes("\r\n");
    }
    
    void writeMain(DataOutputStream out) throws IOException {
        String vername = Attributes$Name.MANIFEST_VERSION.toString();
        String version = getValue(vername);
        if (version == null) {
            vername = Attributes$Name.SIGNATURE_VERSION.toString();
            version = getValue(vername);
        }
        if (version != null) {
            out.writeBytes(vername + ": " + version + "\r\n");
        }
        Iterator it = entrySet().iterator();
        while (it.hasNext()) {
            Map$Entry e = (Map$Entry)(Map$Entry)it.next();
            String name = ((Attributes$Name)(Attributes$Name)e.getKey()).toString();
            if ((version != null) && !(name.equalsIgnoreCase(vername))) {
                StringBuffer buffer = new StringBuffer(name);
                buffer.append(": ");
                String value = (String)(String)e.getValue();
                if (value != null) {
                    byte[] vb = value.getBytes("UTF8");
                    value = new String(vb, 0, 0, vb.length);
                }
                buffer.append(value);
                buffer.append("\r\n");
                Manifest.make72Safe(buffer);
                out.writeBytes(buffer.toString());
            }
        }
        out.writeBytes("\r\n");
    }
    
    void read(Manifest$FastInputStream is, byte[] lbuf) throws IOException {
        String name = null;
        String value = null;
        byte[] lastline = null;
        int len;
        while ((len = is.readLine(lbuf)) != -1) {
            boolean lineContinued = false;
            if (lbuf[--len] != '\n') {
                throw new IOException("line too long");
            }
            if (len > 0 && lbuf[len - 1] == '\r') {
                --len;
            }
            if (len == 0) {
                break;
            }
            int i = 0;
            if (lbuf[0] == ' ') {
                if (name == null) {
                    throw new IOException("misplaced continuation line");
                }
                lineContinued = true;
                byte[] buf = new byte[lastline.length + len - 1];
                System.arraycopy(lastline, 0, buf, 0, lastline.length);
                System.arraycopy(lbuf, 1, buf, lastline.length, len - 1);
                if (is.peek() == ' ') {
                    lastline = buf;
                    continue;
                }
                value = new String(buf, 0, buf.length, "UTF8");
                lastline = null;
            } else {
                while (lbuf[i++] != ':') {
                    if (i >= len) {
                        throw new IOException("invalid header field");
                    }
                }
                if (lbuf[i++] != ' ') {
                    throw new IOException("invalid header field");
                }
                name = new String(lbuf, 0, 0, i - 2);
                if (is.peek() == ' ') {
                    lastline = new byte[len - i];
                    System.arraycopy(lbuf, i, lastline, 0, len - i);
                    continue;
                }
                value = new String(lbuf, i, len - i, "UTF8");
            }
            try {
                if ((putValue(name, value) != null) && (!lineContinued)) {
                    Logger.getLogger("java.util.jar").warning("Duplicate name in Manifest: " + name);
                }
            } catch (IllegalArgumentException e) {
                throw new IOException("invalid header field name: " + name);
            }
        }
    }
    {
    }
}
