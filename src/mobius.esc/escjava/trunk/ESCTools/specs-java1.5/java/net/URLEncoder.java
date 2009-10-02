package java.net;

import java.io.UnsupportedEncodingException;
import java.io.CharArrayWriter;
import java.nio.charset.Charset;
import java.nio.charset.IllegalCharsetNameException;
import java.nio.charset.UnsupportedCharsetException;
import java.util.BitSet;
import java.security.AccessController;
import sun.security.action.GetPropertyAction;

public class URLEncoder {
    static BitSet dontNeedEncoding;
    static final int caseDiff = ('a' - 'A');
    static String dfltEncName = null;
    static {
        dontNeedEncoding = new BitSet(256);
        int i;
        for (i = 'a'; i <= 'z'; i++) {
            dontNeedEncoding.set(i);
        }
        for (i = 'A'; i <= 'Z'; i++) {
            dontNeedEncoding.set(i);
        }
        for (i = '0'; i <= '9'; i++) {
            dontNeedEncoding.set(i);
        }
        dontNeedEncoding.set(' ');
        dontNeedEncoding.set('-');
        dontNeedEncoding.set('_');
        dontNeedEncoding.set('.');
        dontNeedEncoding.set('*');
        dfltEncName = (String)(String)AccessController.doPrivileged(new GetPropertyAction("file.encoding"));
    }
    
    private URLEncoder() {
        
    }
    
    
    public static String encode(String s) {
        String str = null;
        try {
            str = encode(s, dfltEncName);
        } catch (UnsupportedEncodingException e) {
        }
        return str;
    }
    
    public static String encode(String s, String enc) throws UnsupportedEncodingException {
        boolean needToChange = false;
        StringBuffer out = new StringBuffer(s.length());
        Charset charset;
        CharArrayWriter charArrayWriter = new CharArrayWriter();
        if (enc == null) throw new NullPointerException("charsetName");
        try {
            charset = Charset.forName(enc);
        } catch (IllegalCharsetNameException e) {
            throw new UnsupportedEncodingException(enc);
        } catch (UnsupportedCharsetException e) {
            throw new UnsupportedEncodingException(enc);
        }
        for (int i = 0; i < s.length(); ) {
            int c = (int)s.charAt(i);
            if (dontNeedEncoding.get(c)) {
                if (c == ' ') {
                    c = '+';
                    needToChange = true;
                }
                out.append((char)c);
                i++;
            } else {
                do {
                    charArrayWriter.write(c);
                    if (c >= 55296 && c <= 56319) {
                        if ((i + 1) < s.length()) {
                            int d = (int)s.charAt(i + 1);
                            if (d >= 56320 && d <= 57343) {
                                charArrayWriter.write(d);
                                i++;
                            }
                        }
                    }
                    i++;
                }                 while (i < s.length() && !dontNeedEncoding.get((c = (int)s.charAt(i))));
                charArrayWriter.flush();
                String str = new String(charArrayWriter.toCharArray());
                byte[] ba = str.getBytes(charset.name());
                for (int j = 0; j < ba.length; j++) {
                    out.append('%');
                    char ch = Character.forDigit((ba[j] >> 4) & 15, 16);
                    if (Character.isLetter(ch)) {
                        ch -= caseDiff;
                    }
                    out.append(ch);
                    ch = Character.forDigit(ba[j] & 15, 16);
                    if (Character.isLetter(ch)) {
                        ch -= caseDiff;
                    }
                    out.append(ch);
                }
                charArrayWriter.reset();
                needToChange = true;
            }
        }
        return (needToChange ? out.toString() : s);
    }
}
