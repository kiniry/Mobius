package java.util.regex;

public final class Matcher implements MatchResult {
    Pattern parentPattern;
    int[] groups;
    int from;
    int to;
    CharSequence text;
    static final int ENDANCHOR = 1;
    static final int NOANCHOR = 0;
    int acceptMode = NOANCHOR;
    int first = -1;
    int last = 0;
    int oldLast = -1;
    int lastAppendPosition = 0;
    int[] locals;
    boolean hitEnd;
    boolean requireEnd;
    boolean transparentBounds = false;
    boolean anchoringBounds = true;
    
    Matcher() {
        
    }
    
    Matcher(Pattern parent, CharSequence text) {
        
        this.parentPattern = parent;
        this.text = text;
        int parentGroupCount = Math.max(parent.capturingGroupCount, 10);
        groups = new int[parentGroupCount * 2];
        locals = new int[parent.localCount];
        reset();
    }
    
    public Pattern pattern() {
        return parentPattern;
    }
    
    public MatchResult toMatchResult() {
        Matcher result = new Matcher(this.parentPattern, text.toString());
        result.first = this.first;
        result.last = this.last;
        result.groups = (int[])((int[])this.groups.clone());
        return result;
    }
    
    public Matcher usePattern(Pattern newPattern) {
        if (newPattern == null) throw new IllegalArgumentException("Pattern cannot be null");
        parentPattern = newPattern;
        int parentGroupCount = Math.max(newPattern.capturingGroupCount, 10);
        groups = new int[parentGroupCount * 2];
        locals = new int[newPattern.localCount];
        for (int i = 0; i < groups.length; i++) groups[i] = -1;
        for (int i = 0; i < locals.length; i++) locals[i] = -1;
        return this;
    }
    
    public Matcher reset() {
        first = -1;
        last = 0;
        oldLast = -1;
        for (int i = 0; i < groups.length; i++) groups[i] = -1;
        for (int i = 0; i < locals.length; i++) locals[i] = -1;
        lastAppendPosition = 0;
        from = 0;
        to = getTextLength();
        return this;
    }
    
    public Matcher reset(CharSequence input) {
        text = input;
        return reset();
    }
    
    public int start() {
        if (first < 0) throw new IllegalStateException("No match available");
        return first;
    }
    
    public int start(int group) {
        if (first < 0) throw new IllegalStateException("No match available");
        if (group > groupCount()) throw new IndexOutOfBoundsException("No group " + group);
        return groups[group * 2];
    }
    
    public int end() {
        if (first < 0) throw new IllegalStateException("No match available");
        return last;
    }
    
    public int end(int group) {
        if (first < 0) throw new IllegalStateException("No match available");
        if (group > groupCount()) throw new IndexOutOfBoundsException("No group " + group);
        return groups[group * 2 + 1];
    }
    
    public String group() {
        return group(0);
    }
    
    public String group(int group) {
        if (first < 0) throw new IllegalStateException("No match found");
        if (group < 0 || group > groupCount()) throw new IndexOutOfBoundsException("No group " + group);
        if ((groups[group * 2] == -1) || (groups[group * 2 + 1] == -1)) return null;
        return getSubSequence(groups[group * 2], groups[group * 2 + 1]).toString();
    }
    
    public int groupCount() {
        return parentPattern.capturingGroupCount - 1;
    }
    
    public boolean matches() {
        return match(from, ENDANCHOR);
    }
    
    public boolean find() {
        int nextSearchIndex = last;
        if (nextSearchIndex == first) nextSearchIndex++;
        if (nextSearchIndex < from) nextSearchIndex = from;
        if (nextSearchIndex > to) {
            for (int i = 0; i < groups.length; i++) groups[i] = -1;
            return false;
        }
        return search(nextSearchIndex);
    }
    
    public boolean find(int start) {
        int limit = getTextLength();
        if ((start < 0) || (start > limit)) throw new IndexOutOfBoundsException("Illegal start index");
        reset();
        return search(start);
    }
    
    public boolean lookingAt() {
        return match(from, NOANCHOR);
    }
    
    public static String quoteReplacement(String s) {
        if ((s.indexOf('\\') == -1) && (s.indexOf('$') == -1)) return s;
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '\\') {
                sb.append('\\');
                sb.append('\\');
            } else if (c == '$') {
                sb.append('\\');
                sb.append('$');
            } else {
                sb.append(c);
            }
        }
        return sb.toString();
    }
    
    public Matcher appendReplacement(StringBuffer sb, String replacement) {
        if (first < 0) throw new IllegalStateException("No match available");
        int cursor = 0;
        String s = replacement;
        StringBuffer result = new StringBuffer();
        while (cursor < replacement.length()) {
            char nextChar = replacement.charAt(cursor);
            if (nextChar == '\\') {
                cursor++;
                nextChar = replacement.charAt(cursor);
                result.append(nextChar);
                cursor++;
            } else if (nextChar == '$') {
                cursor++;
                int refNum = (int)replacement.charAt(cursor) - '0';
                if ((refNum < 0) || (refNum > 9)) throw new IllegalArgumentException("Illegal group reference");
                cursor++;
                boolean done = false;
                while (!done) {
                    if (cursor >= replacement.length()) {
                        break;
                    }
                    int nextDigit = replacement.charAt(cursor) - '0';
                    if ((nextDigit < 0) || (nextDigit > 9)) {
                        break;
                    }
                    int newRefNum = (refNum * 10) + nextDigit;
                    if (groupCount() < newRefNum) {
                        done = true;
                    } else {
                        refNum = newRefNum;
                        cursor++;
                    }
                }
                if (group(refNum) != null) result.append(group(refNum));
            } else {
                result.append(nextChar);
                cursor++;
            }
        }
        sb.append(getSubSequence(lastAppendPosition, first));
        sb.append(result.toString());
        lastAppendPosition = last;
        return this;
    }
    
    public StringBuffer appendTail(StringBuffer sb) {
        sb.append(getSubSequence(lastAppendPosition, getTextLength()).toString());
        return sb;
    }
    
    public String replaceAll(String replacement) {
        reset();
        boolean result = find();
        if (result) {
            StringBuffer sb = new StringBuffer();
            do {
                appendReplacement(sb, replacement);
                result = find();
            }             while (result);
            appendTail(sb);
            return sb.toString();
        }
        return text.toString();
    }
    
    public String replaceFirst(String replacement) {
        if (replacement == null) throw new NullPointerException("replacement");
        StringBuffer sb = new StringBuffer();
        reset();
        if (find()) appendReplacement(sb, replacement);
        appendTail(sb);
        return sb.toString();
    }
    
    public Matcher region(int start, int end) {
        if ((start < 0) || (start > getTextLength())) throw new IndexOutOfBoundsException("start");
        if ((end < 0) || (end > getTextLength())) throw new IndexOutOfBoundsException("end");
        if (start > end) throw new IndexOutOfBoundsException("start > end");
        reset();
        from = start;
        to = end;
        return this;
    }
    
    public int regionStart() {
        return from;
    }
    
    public int regionEnd() {
        return to;
    }
    
    public boolean hasTransparentBounds() {
        return transparentBounds;
    }
    
    public Matcher useTransparentBounds(boolean b) {
        transparentBounds = b;
        return this;
    }
    
    public boolean hasAnchoringBounds() {
        return anchoringBounds;
    }
    
    public Matcher useAnchoringBounds(boolean b) {
        anchoringBounds = b;
        return this;
    }
    
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("java.util.regex.Matcher");
        sb.append("[pattern=" + pattern());
        sb.append(" region=");
        sb.append(regionStart() + "," + regionEnd());
        sb.append(" lastmatch=");
        if ((first >= 0) && (group() != null)) {
            sb.append(group());
        }
        sb.append("]");
        return sb.toString();
    }
    
    public boolean hitEnd() {
        return hitEnd;
    }
    
    public boolean requireEnd() {
        return requireEnd;
    }
    
    boolean search(int from) {
        this.hitEnd = false;
        this.requireEnd = false;
        from = from < 0 ? 0 : from;
        this.first = from;
        this.oldLast = oldLast < 0 ? from : oldLast;
        for (int i = 0; i < groups.length; i++) groups[i] = -1;
        acceptMode = NOANCHOR;
        boolean result = parentPattern.root.match(this, from, text);
        if (!result) this.first = -1;
        this.oldLast = this.last;
        return result;
    }
    
    boolean match(int from, int anchor) {
        this.hitEnd = false;
        this.requireEnd = false;
        from = from < 0 ? 0 : from;
        this.first = from;
        this.oldLast = oldLast < 0 ? from : oldLast;
        for (int i = 0; i < groups.length; i++) groups[i] = -1;
        acceptMode = anchor;
        boolean result = parentPattern.matchRoot.match(this, from, text);
        if (!result) this.first = -1;
        this.oldLast = this.last;
        return result;
    }
    
    int getTextLength() {
        return text.length();
    }
    
    CharSequence getSubSequence(int beginIndex, int endIndex) {
        return text.subSequence(beginIndex, endIndex);
    }
    
    char charAt(int i) {
        return text.charAt(i);
    }
}
