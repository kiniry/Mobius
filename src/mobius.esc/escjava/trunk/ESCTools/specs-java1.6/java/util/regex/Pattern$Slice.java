package java.util.regex;

class Pattern$Slice extends Pattern$Node {
    int[] buffer;
    
    Pattern$Slice(int[] buf) {
        
        buffer = buf;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int[] buf = buffer;
        int len = buf.length;
        for (int j = 0; j < len; j++) {
            if ((i + j) >= matcher.to) {
                matcher.hitEnd = true;
                return false;
            }
            if (buf[j] != seq.charAt(i + j)) return false;
        }
        return next.match(matcher, i + len, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength += buffer.length;
        info.maxLength += buffer.length;
        return next.study(info);
    }
}
