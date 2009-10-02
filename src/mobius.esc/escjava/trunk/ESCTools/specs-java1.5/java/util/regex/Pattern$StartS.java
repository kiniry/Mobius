package java.util.regex;

final class Pattern$StartS extends Pattern$Start {
    
    Pattern$StartS(Pattern$Node node) {
        super(node);
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i > matcher.to - minLength) {
            matcher.hitEnd = true;
            return false;
        }
        boolean ret = false;
        int guard = matcher.to - minLength;
        while (i <= guard) {
            if ((ret = next.match(matcher, i, seq)) || i == guard) break;
            if (Character.isHighSurrogate(seq.charAt(i++))) {
                if (i < seq.length() && Character.isLowSurrogate(seq.charAt(i))) {
                    i++;
                }
            }
            if (i == guard) matcher.hitEnd = true;
        }
        if (ret) {
            matcher.first = i;
            matcher.groups[0] = matcher.first;
            matcher.groups[1] = matcher.last;
        }
        return ret;
    }
}
