package java.net;

import java.io.*;

public class URLDecoder {
    
    public URLDecoder() {
        
    }
    static String dfltEncName = URLEncoder.dfltEncName;
    
    
    public static String decode(String s) {
        String str = null;
        try {
            str = decode(s, dfltEncName);
        } catch (UnsupportedEncodingException e) {
        }
        return str;
    }
    
    public static String decode(String s, String enc) throws UnsupportedEncodingException {
        boolean needToChange = false;
        int numChars = s.length();
        StringBuffer sb = new StringBuffer(numChars > 500 ? numChars / 2 : numChars);
        int i = 0;
        if (enc.length() == 0) {
            throw new UnsupportedEncodingException("URLDecoder: empty string enc parameter");
        }
        char c;
        byte[] bytes = null;
        while (i < numChars) {
            c = s.charAt(i);
            switch (c) {
            case '+': 
                sb.append(' ');
                i++;
                needToChange = true;
                break;
            
            case '%': 
                try {
                    if (bytes == null) bytes = new byte[(numChars - i) / 3];
                    int pos = 0;
                    while (((i + 2) < numChars) && (c == '%')) {
                        bytes[pos++] = (byte)Integer.parseInt(s.substring(i + 1, i + 3), 16);
                        i += 3;
                        if (i < numChars) c = s.charAt(i);
                    }
                    if ((i < numChars) && (c == '%')) throw new IllegalArgumentException("URLDecoder: Incomplete trailing escape (%) pattern");
                    sb.append(new String(bytes, 0, pos, enc));
                } catch (NumberFormatException e) {
                    throw new IllegalArgumentException("URLDecoder: Illegal hex characters in escape (%) pattern - " + e.getMessage());
                }
                needToChange = true;
                break;
            
            default: 
                sb.append(c);
                i++;
                break;
            
            }
        }
        return (needToChange ? sb.toString() : s);
    }
}
