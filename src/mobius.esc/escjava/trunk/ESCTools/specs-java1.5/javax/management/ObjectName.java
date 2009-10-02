package javax.management;

import java.io.InvalidObjectException;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamField;
import java.io.Serializable;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Hashtable;
import com.sun.jmx.mbeanserver.GetPropertyAction;

public class ObjectName implements QueryExp, Serializable {
    {
    }
    private static final long oldSerialVersionUID = -5467795090068647408L;
    private static final long newSerialVersionUID = 1081892073854801359L;
    private static final ObjectStreamField[] oldSerialPersistentFields = {new ObjectStreamField("domain", String.class), new ObjectStreamField("propertyList", Hashtable.class), new ObjectStreamField("propertyListString", String.class), new ObjectStreamField("canonicalName", String.class), new ObjectStreamField("pattern", Boolean.TYPE), new ObjectStreamField("propertyPattern", Boolean.TYPE)};
    private static final ObjectStreamField[] newSerialPersistentFields = {};
    private static final long serialVersionUID;
    private static final ObjectStreamField[] serialPersistentFields;
    private static boolean compat = false;
    static {
        try {
            PrivilegedAction act = new GetPropertyAction("jmx.serial.form");
            String form = (String)(String)AccessController.doPrivileged(act);
            compat = (form != null && form.equals("1.0"));
        } catch (Exception e) {
        }
        if (compat) {
            serialPersistentFields = oldSerialPersistentFields;
            serialVersionUID = oldSerialVersionUID;
        } else {
            serialPersistentFields = newSerialPersistentFields;
            serialVersionUID = newSerialVersionUID;
        }
    }
    private static final ObjectName$Property[] _Empty_property_array = new ObjectName$Property[0];
    private static final Hashtable _EmptyPropertyList = new Hashtable(1);
    private transient String _canonicalName;
    private transient ObjectName$Property[] _kp_array;
    private transient ObjectName$Property[] _ca_array;
    private transient int _domain_length = 0;
    private transient Hashtable _propertyList;
    private transient boolean _domain_pattern = false;
    private transient boolean _property_pattern = false;
    
    private void construct(String name) throws MalformedObjectNameException, NullPointerException {
        if (name == null) throw new NullPointerException("name cannot be null");
        if (name.length() == 0) {
            _canonicalName = "*:*";
            _kp_array = _Empty_property_array;
            _ca_array = _Empty_property_array;
            _domain_length = 1;
            _propertyList = null;
            _domain_pattern = true;
            _property_pattern = true;
            return;
        }
        char[] name_chars = name.toCharArray();
        int len = name_chars.length;
        char[] canonical_chars = new char[len];
        int cname_index = 0;
        int index = 0;
        char c;
        char c1;
        domain_parsing: while (index < len) {
            switch (c = name_chars[index]) {
            case ':': 
                _domain_length = index++;
                break domain_parsing;
            
            case '=': 
                int i = ++index;
                while ((i < len) && (name_chars[i++] != ':')) if (i == len) throw new MalformedObjectNameException("Domain part must be specified");
                break;
            
            case '\n': 
                throw new MalformedObjectNameException("Invalid character \'\\n\' in domain name");
            
            case '*': 
            
            case '?': 
                _domain_pattern = true;
            
            default: 
                index++;
            
            }
        }
        if (index == len) throw new MalformedObjectNameException("Key properties cannot be empty");
        System.arraycopy(name_chars, 0, canonical_chars, 0, _domain_length);
        canonical_chars[_domain_length] = ':';
        cname_index = _domain_length + 1;
        ObjectName$Property prop;
        HashMap keys_map = new HashMap();
        String[] keys;
        String key_name;
        boolean quoted_value;
        int property_index = 0;
        int in_index;
        int key_index;
        int key_length;
        int value_index;
        int value_length;
        keys = new String[10];
        _kp_array = new ObjectName$Property[10];
        _property_pattern = false;
        while (index < len) {
            c = name_chars[index];
            if (c == '*') {
                if (_property_pattern) throw new MalformedObjectNameException("Cannot have several \'*\' characters in pattern properties"); else {
                    _property_pattern = true;
                    if ((++index < len) && (name_chars[index] != ',')) throw new MalformedObjectNameException("Invalid character found after \'*\': end of name or \',\' expected"); else if (index == len) {
                        if (property_index == 0) {
                            _kp_array = _Empty_property_array;
                            _ca_array = _Empty_property_array;
                            _propertyList = _EmptyPropertyList;
                        }
                        break;
                    } else {
                        index++;
                        continue;
                    }
                }
            }
            in_index = index;
            key_index = in_index;
            while ((in_index < len) && ((c1 = name_chars[in_index++]) != '=')) switch (c1) {
            case '*': 
            
            case '?': 
            
            case ',': 
            
            case ':': 
            
            case '\n': 
                final String ichar = ((c1 == '\n') ? "\\n" : "" + c1);
                throw new MalformedObjectNameException("Invalid character \'" + ichar + "\' in key part of property");
            
            default: 
                ;
            
            }
            if (in_index == len) throw new MalformedObjectNameException("Unterminated key property part");
            if (in_index == index) throw new MalformedObjectNameException("Invalid key (empty)");
            value_index = in_index;
            key_length = value_index - key_index - 1;
            if (name_chars[in_index] == '\"') {
                quoted_value = true;
                quoted_value_parsing: while ((++in_index < len) && ((c1 = name_chars[in_index]) != '\"')) {
                    if (c1 == '\\') {
                        if (++in_index == len) throw new MalformedObjectNameException("Unterminated quoted value");
                        switch (c1 = name_chars[in_index]) {
                        case '\\': 
                        
                        case '\"': 
                        
                        case '?': 
                        
                        case '*': 
                        
                        case 'n': 
                            break;
                        
                        default: 
                            throw new MalformedObjectNameException("Invalid escape sequence \'\\" + c1 + "\' in quoted value");
                        
                        }
                    } else if (c1 == '\n') {
                        throw new MalformedObjectNameException("Newline in quoted value");
                    } else {
                        switch (c1) {
                        case '?': 
                        
                        case '*': 
                            throw new MalformedObjectNameException("Invalid unescaped reserved character \'" + c1 + "\' in quoted value");
                        
                        default: 
                            break;
                        
                        }
                    }
                }
                if (in_index == len) throw new MalformedObjectNameException("Unterminated quoted value"); else value_length = ++in_index - value_index;
            } else {
                quoted_value = false;
                while ((in_index < len) && ((c1 = name_chars[in_index]) != ',')) switch (c1) {
                case '*': 
                
                case '?': 
                
                case '=': 
                
                case ':': 
                
                case '\"': 
                
                case '\n': 
                    final String ichar = ((c1 == '\n') ? "\\n" : "" + c1);
                    throw new MalformedObjectNameException("Invalid character \'" + c1 + "\' in value part of property");
                
                default: 
                    in_index++;
                
                }
                value_length = in_index - value_index;
            }
            if (in_index == len - 1) {
                if (quoted_value) throw new MalformedObjectNameException("Invalid ending character `" + name_chars[in_index] + "\'"); else throw new MalformedObjectNameException("Invalid ending comma");
            } else in_index++;
            prop = new ObjectName$Property(key_index, key_length, value_length);
            key_name = name.substring(key_index, key_index + key_length);
            if (property_index == keys.length) {
                String[] tmp_string_array = new String[property_index + 10];
                System.arraycopy(keys, 0, tmp_string_array, 0, property_index);
                keys = tmp_string_array;
            }
            keys[property_index] = key_name;
            addProperty(prop, property_index, keys_map, key_name);
            property_index++;
            index = in_index;
        }
        setCanonicalName(name_chars, canonical_chars, keys, keys_map, cname_index, property_index);
    }
    
    private void construct(String domain, Hashtable props) throws MalformedObjectNameException, NullPointerException {
        if (domain == null) throw new NullPointerException("domain cannot be null");
        if (props == null) throw new NullPointerException("key property list cannot be null");
        if (props.isEmpty()) throw new MalformedObjectNameException("key property list cannot be empty");
        if (!isDomain(domain)) throw new MalformedObjectNameException("Invalid domain: " + domain);
        final StringBuffer sb = new StringBuffer();
        sb.append(domain).append(':');
        _domain_length = domain.length();
        int nb_props = props.size();
        _kp_array = new ObjectName$Property[nb_props];
        String[] keys = new String[nb_props];
        final Enumeration e = props.keys();
        final HashMap keys_map = new HashMap();
        ObjectName$Property prop;
        int key_index;
        for (int i = 0; e.hasMoreElements(); i++) {
            if (i > 0) sb.append(",");
            String key = "";
            try {
                key = (String)(String)e.nextElement();
            } catch (Exception x) {
                throw new MalformedObjectNameException("Invalid key `" + key + "\'");
            }
            String value = "";
            try {
                value = (String)(String)props.get(key);
            } catch (Exception x) {
                throw new MalformedObjectNameException("Invalid value `" + value + "\'");
            }
            key_index = sb.length();
            checkKey(key);
            sb.append(key);
            keys[i] = key;
            sb.append("=");
            checkValue(value);
            sb.append(value);
            prop = new ObjectName$Property(key_index, key.length(), value.length());
            addProperty(prop, i, keys_map, key);
        }
        int len = sb.length();
        char[] initial_chars = new char[len];
        sb.getChars(0, len, initial_chars, 0);
        char[] canonical_chars = new char[len];
        System.arraycopy(initial_chars, 0, canonical_chars, 0, _domain_length + 1);
        setCanonicalName(initial_chars, canonical_chars, keys, keys_map, _domain_length + 1, _kp_array.length);
    }
    
    private void addProperty(ObjectName$Property prop, int index, HashMap keys_map, String key_name) throws MalformedObjectNameException {
        if (keys_map.containsKey(key_name)) throw new MalformedObjectNameException("key `" + key_name + "\' already defined");
        if (index == _kp_array.length) {
            ObjectName$Property[] tmp_prop_array = new ObjectName$Property[index + 10];
            System.arraycopy(_kp_array, 0, tmp_prop_array, 0, index);
            _kp_array = tmp_prop_array;
        }
        _kp_array[index] = prop;
        keys_map.put(key_name, prop);
    }
    
    private void setCanonicalName(char[] specified_chars, char[] canonical_chars, String[] keys, HashMap keys_map, int prop_index, int nb_props) {
        if (_kp_array != _Empty_property_array) {
            String[] tmp_keys = new String[nb_props];
            ObjectName$Property[] tmp_props = new ObjectName$Property[nb_props];
            System.arraycopy(keys, 0, tmp_keys, 0, nb_props);
            Arrays.sort(tmp_keys);
            keys = tmp_keys;
            System.arraycopy(_kp_array, 0, tmp_props, 0, nb_props);
            _kp_array = tmp_props;
            _ca_array = new ObjectName$Property[nb_props];
            for (int i = 0; i < nb_props; i++) _ca_array[i] = (ObjectName$Property)(ObjectName$Property)keys_map.get(keys[i]);
            int last_index = nb_props - 1;
            int prop_len;
            ObjectName$Property prop;
            for (int i = 0; i <= last_index; i++) {
                prop = _ca_array[i];
                prop_len = prop._key_length + prop._value_length + 1;
                System.arraycopy(specified_chars, prop._key_index, canonical_chars, prop_index, prop_len);
                prop.setKeyIndex(prop_index);
                prop_index += prop_len;
                if (i != last_index) {
                    canonical_chars[prop_index] = ',';
                    prop_index++;
                }
            }
        }
        if (_property_pattern) {
            if (_kp_array != _Empty_property_array) canonical_chars[prop_index++] = ',';
            canonical_chars[prop_index++] = '*';
        }
        _canonicalName = (new String(canonical_chars, 0, prop_index)).intern();
    }
    
    private static final int parseKey(final char[] s, final int startKey) throws MalformedObjectNameException {
        int next = startKey;
        int endKey = startKey;
        final int len = s.length;
        while (next < len) {
            final char k = s[next++];
            switch (k) {
            case '*': 
            
            case '?': 
            
            case ',': 
            
            case ':': 
            
            case '\n': 
                final String ichar = ((k == '\n') ? "\\n" : "" + k);
                throw new MalformedObjectNameException("Invalid character in key: `" + ichar + "\'");
            
            case '=': 
                endKey = next - 1;
                break;
            
            default: 
                if (next < len) continue; else endKey = next;
            
            }
            break;
        }
        return endKey;
    }
    
    private static final int parseValue(final char[] s, final int startValue) throws MalformedObjectNameException {
        int next = startValue;
        int endValue = startValue;
        final int len = s.length;
        final char q = s[startValue];
        if (q == '\"') {
            if (++next == len) throw new MalformedObjectNameException("Invalid quote");
            while (next < len) {
                char last = s[next];
                if (last == '\\') {
                    if (++next == len) throw new MalformedObjectNameException("Invalid unterminated quoted character sequence");
                    last = s[next];
                    switch (last) {
                    case '\\': 
                    
                    case '?': 
                    
                    case '*': 
                    
                    case 'n': 
                        break;
                    
                    case '\"': 
                        if (next + 1 == len) throw new MalformedObjectNameException("Missing termination quote");
                        break;
                    
                    default: 
                        throw new MalformedObjectNameException("Invalid quoted character sequence \'\\" + last + "\'");
                    
                    }
                } else if (last == '\n') {
                    throw new MalformedObjectNameException("Newline in quoted value");
                } else if (last == '\"') {
                    next++;
                    break;
                } else {
                    switch (last) {
                    case '?': 
                    
                    case '*': 
                        throw new MalformedObjectNameException("Invalid unescaped reserved character \'" + last + "\' in quoted value");
                    
                    default: 
                        break;
                    
                    }
                }
                next++;
                if ((next >= len) && (last != '\"')) throw new MalformedObjectNameException("Missing termination quote");
            }
            endValue = next;
            if (next < len) {
                if (s[next++] != ',') throw new MalformedObjectNameException("Invalid quote");
            }
        } else {
            while (next < len) {
                final char v = s[next++];
                switch (v) {
                case '*': 
                
                case '?': 
                
                case '=': 
                
                case ':': 
                
                case '\n': 
                    final String ichar = ((v == '\n') ? "\\n" : "" + v);
                    throw new MalformedObjectNameException("Invalid character `" + ichar + "\' in value");
                
                case ',': 
                    endValue = next - 1;
                    break;
                
                default: 
                    if (next < len) continue; else endValue = next;
                
                }
                break;
            }
        }
        return endValue;
    }
    
    private String checkValue(String val) throws MalformedObjectNameException {
        if (val == null) throw new MalformedObjectNameException("Invalid value (null)");
        final int len = val.length();
        if (len == 0) throw new MalformedObjectNameException("Invalid value (empty)");
        final char[] s = val.toCharArray();
        final int endValue = parseValue(s, 0);
        if (endValue < len) throw new MalformedObjectNameException("Invalid character in value: `" + s[endValue] + "\'");
        return val;
    }
    
    private String checkKey(String key) throws MalformedObjectNameException {
        if (key == null) throw new MalformedObjectNameException("Invalid key (null)");
        final int len = key.length();
        if (len == 0) throw new MalformedObjectNameException("Invalid key (empty)");
        final char[] k = key.toCharArray();
        final int endKey = parseKey(k, 0);
        if (endKey < len) throw new MalformedObjectNameException("Invalid character in value: `" + k[endKey] + "\'");
        return key;
    }
    
    private static boolean wildmatch(char[] s, char[] p, int si, int pi) {
        char c;
        final int slen = s.length;
        final int plen = p.length;
        while (pi < plen) {
            c = p[pi++];
            if (c == '?') {
                if (++si > slen) return false;
            } else if (c == '*') {
                if (pi >= plen) return true;
                do {
                    if (wildmatch(s, p, si, pi)) return true;
                }                 while (++si < slen);
                return false;
            } else {
                if (si >= slen || c != s[si++]) return false;
            }
        }
        return (si == slen);
    }
    
    private boolean isDomain(String domain) {
        if (domain == null) return true;
        final char[] d = domain.toCharArray();
        final int len = d.length;
        int next = 0;
        while (next < len) {
            final char c = d[next++];
            switch (c) {
            case ':': 
            
            case '\n': 
                return false;
            
            case '*': 
            
            case '?': 
                _domain_pattern = true;
            
            default: 
                continue;
            
            }
        }
        return true;
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        String cn;
        if (compat) {
            final ObjectInputStream$GetField fields = in.readFields();
            String propListString = (String)(String)fields.get("propertyListString", "");
            final boolean propPattern = fields.get("propertyPattern", false);
            if (propPattern) {
                propListString = (propListString.length() == 0 ? "*" : (propListString + ",*"));
            }
            cn = (String)(String)fields.get("domain", "default") + ":" + propListString;
        } else {
            in.defaultReadObject();
            cn = (String)(String)in.readObject();
        }
        try {
            construct(cn);
        } catch (NullPointerException e) {
            throw new InvalidObjectException(e.toString());
        } catch (MalformedObjectNameException e) {
            throw new InvalidObjectException(e.toString());
        }
    }
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        if (compat) {
            ObjectOutputStream$PutField fields = out.putFields();
            fields.put("domain", _canonicalName.substring(0, _domain_length));
            fields.put("propertyList", getKeyPropertyList());
            fields.put("propertyListString", getKeyPropertyListString());
            fields.put("canonicalName", _canonicalName);
            fields.put("pattern", (_domain_pattern || _property_pattern));
            fields.put("propertyPattern", _property_pattern);
            out.writeFields();
        } else {
            out.defaultWriteObject();
            out.writeObject(getSerializedNameString());
        }
    }
    
    public static ObjectName getInstance(String name) throws MalformedObjectNameException, NullPointerException {
        return new ObjectName(name);
    }
    
    public static ObjectName getInstance(String domain, String key, String value) throws MalformedObjectNameException, NullPointerException {
        return new ObjectName(domain, key, value);
    }
    
    public static ObjectName getInstance(String domain, Hashtable table) throws MalformedObjectNameException, NullPointerException {
        return new ObjectName(domain, table);
    }
    
    public static ObjectName getInstance(ObjectName name) throws NullPointerException {
        if (name.getClass().equals(ObjectName.class)) return name;
        try {
            return new ObjectName(name.getSerializedNameString());
        } catch (MalformedObjectNameException e) {
            throw new IllegalArgumentException("Unexpected: " + e);
        }
    }
    
    public ObjectName(String name) throws MalformedObjectNameException, NullPointerException {
        
        construct(name);
    }
    
    public ObjectName(String domain, String key, String value) throws MalformedObjectNameException, NullPointerException {
        
        Hashtable table = new Hashtable(1);
        table.put(key, value);
        construct(domain, table);
    }
    
    public ObjectName(String domain, Hashtable table) throws MalformedObjectNameException, NullPointerException {
        
        construct(domain, table);
    }
    
    public boolean isPattern() {
        return (_domain_pattern || _property_pattern);
    }
    
    public boolean isDomainPattern() {
        return _domain_pattern;
    }
    
    public boolean isPropertyPattern() {
        return _property_pattern;
    }
    
    public String getCanonicalName() {
        return _canonicalName;
    }
    
    public String getDomain() {
        return _canonicalName.substring(0, _domain_length);
    }
    
    public String getKeyProperty(String property) throws NullPointerException {
        return (String)(String)_getKeyPropertyList().get(property);
    }
    
    private final Hashtable _getKeyPropertyList() {
        synchronized (this) {
            if (_propertyList == null) {
                _propertyList = new Hashtable();
                int len = _ca_array.length;
                ObjectName$Property prop;
                for (int i = len - 1; i >= 0; i--) {
                    prop = _ca_array[i];
                    _propertyList.put(prop.getKeyString(_canonicalName), prop.getValueString(_canonicalName));
                }
            }
        }
        return _propertyList;
    }
    
    public Hashtable getKeyPropertyList() {
        return (Hashtable)(Hashtable)_getKeyPropertyList().clone();
    }
    
    public String getKeyPropertyListString() {
        if (_kp_array.length == 0) return "";
        final int total_size = _canonicalName.length() - _domain_length - 1 - (_property_pattern ? 2 : 0);
        final char[] dest_chars = new char[total_size];
        final char[] value = _canonicalName.toCharArray();
        writeKeyPropertyListString(value, dest_chars, 0);
        return new String(dest_chars);
    }
    
    private String getSerializedNameString() {
        final int total_size = _canonicalName.length();
        final char[] dest_chars = new char[total_size];
        final char[] value = _canonicalName.toCharArray();
        final int offset = _domain_length + 1;
        System.arraycopy(value, 0, dest_chars, 0, offset);
        final int end = writeKeyPropertyListString(value, dest_chars, offset);
        if (_property_pattern) {
            if (end == offset) {
                dest_chars[end] = '*';
            } else {
                dest_chars[end] = ',';
                dest_chars[end + 1] = '*';
            }
        }
        return new String(dest_chars);
    }
    
    private int writeKeyPropertyListString(char[] canonicalChars, char[] data, int offset) {
        if (_kp_array.length == 0) return offset;
        final char[] dest_chars = data;
        final char[] value = _canonicalName.toCharArray();
        int index = offset;
        final int len = _kp_array.length;
        final int last = len - 1;
        for (int i = 0; i < len; i++) {
            final ObjectName$Property prop = _kp_array[i];
            final int prop_len = prop._key_length + prop._value_length + 1;
            System.arraycopy(value, prop._key_index, dest_chars, index, prop_len);
            index += prop_len;
            if (i < last) dest_chars[index++] = ',';
        }
        return index;
    }
    
    public String getCanonicalKeyPropertyListString() {
        if (_ca_array.length == 0) return "";
        int len = _canonicalName.length();
        if (_property_pattern) len -= 2;
        return _canonicalName.substring(_domain_length + 1, len);
    }
    
    public String toString() {
        return getSerializedNameString();
    }
    
    public boolean equals(Object object) {
        if (this == object) return true;
        if (!(object instanceof ObjectName)) return false;
        ObjectName on = (ObjectName)(ObjectName)object;
        String on_string = on._canonicalName;
        if (_canonicalName == on_string) return true;
        return false;
    }
    
    public int hashCode() {
        return _canonicalName.hashCode();
    }
    
    public static String quote(String s) throws NullPointerException {
        final StringBuffer buf = new StringBuffer("\"");
        final int len = s.length();
        for (int i = 0; i < len; i++) {
            char c = s.charAt(i);
            switch (c) {
            case '\n': 
                c = 'n';
            
            case '\\': 
            
            case '\"': 
            
            case '*': 
            
            case '?': 
                buf.append('\\');
                break;
            
            }
            buf.append(c);
        }
        buf.append('\"');
        return buf.toString();
    }
    
    public static String unquote(String q) throws IllegalArgumentException, NullPointerException {
        final StringBuffer buf = new StringBuffer();
        final int len = q.length();
        if (len < 2 || q.charAt(0) != '\"' || q.charAt(len - 1) != '\"') throw new IllegalArgumentException("Argument not quoted");
        for (int i = 1; i < len - 1; i++) {
            char c = q.charAt(i);
            if (c == '\\') {
                if (i == len - 2) throw new IllegalArgumentException("Trailing backslash");
                c = q.charAt(++i);
                switch (c) {
                case 'n': 
                    c = '\n';
                    break;
                
                case '\\': 
                
                case '\"': 
                
                case '*': 
                
                case '?': 
                    break;
                
                default: 
                    throw new IllegalArgumentException("Bad character \'" + c + "\' after backslash");
                
                }
            } else {
                switch (c) {
                case '*': 
                
                case '?': 
                
                case '\"': 
                
                case '\n': 
                    throw new IllegalArgumentException("Invalid unescaped character \'" + c + "\' in the string to unquote");
                
                default: 
                    ;
                
                }
            }
            buf.append(c);
        }
        return buf.toString();
    }
    
    public boolean apply(ObjectName name) throws NullPointerException {
        if (name == null) throw new NullPointerException();
        if (name._domain_pattern || name._property_pattern) return false;
        if (!_domain_pattern && !_property_pattern) return _canonicalName.equals(name._canonicalName);
        return matchDomains(name) && matchKeys(name);
    }
    
    private final boolean matchDomains(ObjectName name) {
        if (_domain_pattern) {
            final char[] dom_pattern = getDomain().toCharArray();
            final char[] dom_string = name.getDomain().toCharArray();
            return wildmatch(dom_string, dom_pattern, 0, 0);
        }
        return getDomain().equals(name.getDomain());
    }
    
    private final boolean matchKeys(ObjectName name) {
        if (_property_pattern) {
            final Hashtable nameProps = name._getKeyPropertyList();
            final ObjectName$Property[] props = _ca_array;
            final String cn = _canonicalName;
            for (int i = props.length - 1; i >= 0; i--) {
                final ObjectName$Property p = props[i];
                final String k = p.getKeyString(cn);
                final String v = (String)(String)nameProps.get(k);
                if (v == null) return false;
                if (v.equals(p.getValueString(cn))) continue;
                return false;
            }
            return true;
        }
        final String p1 = name.getCanonicalKeyPropertyListString();
        final String p2 = getCanonicalKeyPropertyListString();
        return (p1.equals(p2));
    }
    
    public void setMBeanServer(MBeanServer mbs) {
    }
}
