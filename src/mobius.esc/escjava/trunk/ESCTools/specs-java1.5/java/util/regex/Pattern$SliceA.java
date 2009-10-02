package java.util.regex;

final class Pattern$SliceA extends Pattern$Node {
    int[] buffer;
    
    Pattern$SliceA(int[] buf) {
        
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
            int c = ASCII.toLower(seq.charAt(i + j));
            if (buf[j] != c) return false;
        }
        return next.match(matcher, i + len, seq);
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength += buffer.length;
        info.maxLength += buffer.length;
        return next.study(info);
    }
}
