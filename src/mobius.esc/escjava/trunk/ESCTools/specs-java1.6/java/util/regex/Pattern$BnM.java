package java.util.regex;

class Pattern$BnM extends Pattern$Node {
    int[] buffer;
    int[] lastOcc;
    int[] optoSft;
    
    static Pattern$Node optimize(Pattern$Node node) {
        if (!(node instanceof Pattern$Slice)) {
            return node;
        }
        int[] src = ((Pattern$Slice)(Pattern$Slice)node).buffer;
        int patternLength = src.length;
        if (patternLength < 4) {
            return node;
        }
        int i;
        int j;
        int k;
        int[] lastOcc = new int[128];
        int[] optoSft = new int[patternLength];
        for (i = 0; i < patternLength; i++) {
            lastOcc[src[i] & 127] = i + 1;
        }
        NEXT: for (i = patternLength; i > 0; i--) {
            for (j = patternLength - 1; j >= i; j--) {
                if (src[j] == src[j - i]) {
                    optoSft[j - 1] = i;
                } else {
                    continue NEXT;
                }
            }
            while (j > 0) {
                optoSft[--j] = i;
            }
        }
        optoSft[patternLength - 1] = 1;
        if (node instanceof Pattern$SliceS) return new Pattern$BnMS(src, lastOcc, optoSft, node.next);
        return new Pattern$BnM(src, lastOcc, optoSft, node.next);
    }
    
    Pattern$BnM(int[] src, int[] lastOcc, int[] optoSft, Pattern$Node next) {
        
        this.buffer = src;
        this.lastOcc = lastOcc;
        this.optoSft = optoSft;
        this.next = next;
    }
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        int[] src = buffer;
        int patternLength = src.length;
        int last = matcher.to - patternLength;
        NEXT: while (i <= last) {
            for (int j = patternLength - 1; j >= 0; j--) {
                int ch = seq.charAt(i + j);
                if (ch != src[j]) {
                    i += Math.max(j + 1 - lastOcc[ch & 127], optoSft[j]);
                    continue NEXT;
                }
            }
            matcher.first = i;
            boolean ret = next.match(matcher, i + patternLength, seq);
            if (ret) {
                matcher.first = i;
                matcher.groups[0] = matcher.first;
                matcher.groups[1] = matcher.last;
                return true;
            }
            i++;
        }
        matcher.hitEnd = true;
        return false;
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength += buffer.length;
        info.maxValid = false;
        return next.study(info);
    }
}
