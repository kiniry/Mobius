package java.util.regex;

final class Pattern$BnMS extends Pattern$BnM {
    int lengthInChars;
    
    Pattern$BnMS(int[] src, int[] lastOcc, int[] optoSft, Pattern$Node next) {
        super(src, lastOcc, optoSft, next);
        for (int x = 0; x < buffer.length; x++) {
            lengthInChars += Character.charCount(buffer[x]);
        }
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int[] src = buffer;
        int patternLength = src.length;
        int last = matcher.to - lengthInChars;
        NEXT: while (i <= last) {
            int ch;
            for (int j = Pattern.access$000(seq, i, patternLength), x = patternLength - 1; j > 0; j -= Character.charCount(ch), x--) {
                ch = Character.codePointBefore(seq, i + j);
                if (ch != src[x]) {
                    int n = Math.max(x + 1 - lastOcc[ch & 127], optoSft[x]);
                    i += Pattern.access$000(seq, i, n);
                    continue NEXT;
                }
            }
            matcher.first = i;
            boolean ret = next.match(matcher, i + lengthInChars, seq);
            if (ret) {
                matcher.first = i;
                matcher.groups[0] = matcher.first;
                matcher.groups[1] = matcher.last;
                return true;
            }
            i += Pattern.access$000(seq, i, 1);
        }
        matcher.hitEnd = true;
        return false;
    }
}
