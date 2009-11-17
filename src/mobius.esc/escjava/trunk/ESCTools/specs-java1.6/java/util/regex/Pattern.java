package java.util.regex;

import sun.text.Normalizer;
import java.util.ArrayList;

public final class Pattern implements java.io.Serializable {
    
    /*synthetic*/ static boolean access$100(Matcher x0, int x1, CharSequence x2) {
        return hasBaseCharacter(x0, x1, x2);
    }
    
    /*synthetic*/ static int access$000(CharSequence x0, int x1, int x2) {
        return countChars(x0, x1, x2);
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !Pattern.class.desiredAssertionStatus();
    public static final int UNIX_LINES = 1;
    public static final int CASE_INSENSITIVE = 2;
    public static final int COMMENTS = 4;
    public static final int MULTILINE = 8;
    public static final int LITERAL = 16;
    public static final int DOTALL = 32;
    public static final int UNICODE_CASE = 64;
    public static final int CANON_EQ = 128;
    private static final long serialVersionUID = 5073258162644648461L;
    private String pattern;
    private int flags;
    private volatile transient boolean compiled = false;
    private transient String normalizedPattern;
    transient Pattern$Node root;
    transient Pattern$Node matchRoot;
    transient int[] buffer;
    transient Pattern$GroupHead[] groupNodes;
    private transient int[] temp;
    transient int capturingGroupCount;
    transient int localCount;
    private transient int cursor;
    private transient int patternLength;
    
    public static Pattern compile(String regex) {
        return new Pattern(regex, 0);
    }
    
    public static Pattern compile(String regex, int flags) {
        return new Pattern(regex, flags);
    }
    
    public String pattern() {
        return pattern;
    }
    
    public String toString() {
        return pattern;
    }
    
    public Matcher matcher(CharSequence input) {
        synchronized (this) {
            if (!compiled) compile();
        }
        Matcher m = new Matcher(this, input);
        return m;
    }
    
    public int flags() {
        return flags;
    }
    
    public static boolean matches(String regex, CharSequence input) {
        Pattern p = Pattern.compile(regex);
        Matcher m = p.matcher(input);
        return m.matches();
    }
    
    public String[] split(CharSequence input, int limit) {
        int index = 0;
        boolean matchLimited = limit > 0;
        ArrayList matchList = new ArrayList();
        Matcher m = matcher(input);
        while (m.find()) {
            if (!matchLimited || matchList.size() < limit - 1) {
                String match = input.subSequence(index, m.start()).toString();
                matchList.add(match);
                index = m.end();
            } else if (matchList.size() == limit - 1) {
                String match = input.subSequence(index, input.length()).toString();
                matchList.add(match);
                index = m.end();
            }
        }
        if (index == 0) return new String[]{input.toString()};
        if (!matchLimited || matchList.size() < limit) matchList.add(input.subSequence(index, input.length()).toString());
        int resultSize = matchList.size();
        if (limit == 0) while (resultSize > 0 && matchList.get(resultSize - 1).equals("")) resultSize--;
        String[] result = new String[resultSize];
        return (String[])(String[])matchList.subList(0, resultSize).toArray(result);
    }
    
    public String[] split(CharSequence input) {
        return split(input, 0);
    }
    
    public static String quote(String s) {
        int slashEIndex = s.indexOf("\\E");
        if (slashEIndex == -1) return "\\Q" + s + "\\E";
        StringBuilder sb = new StringBuilder(s.length() * 2);
        sb.append("\\Q");
        slashEIndex = 0;
        int current = 0;
        while ((slashEIndex = s.indexOf("\\E", current)) != -1) {
            sb.append(s.substring(current, slashEIndex));
            current = slashEIndex + 2;
            sb.append("\\E\\\\E\\Q");
        }
        sb.append(s.substring(current, s.length()));
        sb.append("\\E");
        return sb.toString();
    }
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        s.defaultReadObject();
        capturingGroupCount = 1;
        localCount = 0;
        compiled = false;
        if (pattern.length() == 0) {
            root = new Pattern$Start(lastAccept);
            matchRoot = lastAccept;
            compiled = true;
        }
    }
    
    private Pattern(String p, int f) {
        
        pattern = p;
        flags = f;
        capturingGroupCount = 1;
        localCount = 0;
        if (pattern.length() > 0) {
            compile();
        } else {
            root = new Pattern$Start(lastAccept);
            matchRoot = lastAccept;
        }
    }
    
    private void normalize() {
        boolean inCharClass = false;
        int lastCodePoint = -1;
        normalizedPattern = Normalizer.decompose(pattern, false, 0);
        patternLength = normalizedPattern.length();
        StringBuilder newPattern = new StringBuilder(patternLength);
        for (int i = 0; i < patternLength; ) {
            int c = normalizedPattern.codePointAt(i);
            StringBuilder sequenceBuffer;
            if ((Character.getType(c) == Character.NON_SPACING_MARK) && (lastCodePoint != -1)) {
                sequenceBuffer = new StringBuilder();
                sequenceBuffer.appendCodePoint(lastCodePoint);
                sequenceBuffer.appendCodePoint(c);
                while (Character.getType(c) == Character.NON_SPACING_MARK) {
                    i += Character.charCount(c);
                    if (i >= patternLength) break;
                    c = normalizedPattern.codePointAt(i);
                    sequenceBuffer.appendCodePoint(c);
                }
                String ea = produceEquivalentAlternation(sequenceBuffer.toString());
                newPattern.setLength(newPattern.length() - Character.charCount(lastCodePoint));
                newPattern.append("(?:").append(ea).append(")");
            } else if (c == '[' && lastCodePoint != '\\') {
                i = normalizeCharClass(newPattern, i);
            } else {
                newPattern.appendCodePoint(c);
            }
            lastCodePoint = c;
            i += Character.charCount(c);
        }
        normalizedPattern = newPattern.toString();
    }
    
    private int normalizeCharClass(StringBuilder newPattern, int i) {
        StringBuilder charClass = new StringBuilder();
        StringBuilder eq = null;
        int lastCodePoint = -1;
        String result;
        i++;
        charClass.append("[");
        while (true) {
            int c = normalizedPattern.codePointAt(i);
            StringBuilder sequenceBuffer;
            if (c == ']' && lastCodePoint != '\\') {
                charClass.append((char)c);
                break;
            } else if (Character.getType(c) == Character.NON_SPACING_MARK) {
                sequenceBuffer = new StringBuilder();
                sequenceBuffer.appendCodePoint(lastCodePoint);
                while (Character.getType(c) == Character.NON_SPACING_MARK) {
                    sequenceBuffer.appendCodePoint(c);
                    i += Character.charCount(c);
                    if (i >= normalizedPattern.length()) break;
                    c = normalizedPattern.codePointAt(i);
                }
                String ea = produceEquivalentAlternation(sequenceBuffer.toString());
                charClass.setLength(charClass.length() - Character.charCount(lastCodePoint));
                if (eq == null) eq = new StringBuilder();
                eq.append('|');
                eq.append(ea);
            } else {
                charClass.appendCodePoint(c);
                i++;
            }
            if (i == normalizedPattern.length()) error("Unclosed character class");
            lastCodePoint = c;
        }
        if (eq != null) {
            result = new String("(?:" + charClass.toString() + eq.toString() + ")");
        } else {
            result = charClass.toString();
        }
        newPattern.append(result);
        return i;
    }
    
    private String produceEquivalentAlternation(String source) {
        int len = countChars(source, 0, 1);
        if (source.length() == len) return new String(source);
        String base = source.substring(0, len);
        String combiningMarks = source.substring(len);
        String[] perms = producePermutations(combiningMarks);
        StringBuilder result = new StringBuilder(source);
        for (int x = 0; x < perms.length; x++) {
            String next = base + perms[x];
            if (x > 0) result.append("|" + next);
            next = composeOneStep(next);
            if (next != null) result.append("|" + produceEquivalentAlternation(next));
        }
        return result.toString();
    }
    
    private String[] producePermutations(String input) {
        if (input.length() == countChars(input, 0, 1)) return new String[]{input};
        if (input.length() == countChars(input, 0, 2)) {
            int c0 = Character.codePointAt(input, 0);
            int c1 = Character.codePointAt(input, Character.charCount(c0));
            if (getClass(c1) == getClass(c0)) {
                return new String[]{input};
            }
            String[] result = new String[2];
            result[0] = input;
            StringBuilder sb = new StringBuilder(2);
            sb.appendCodePoint(c1);
            sb.appendCodePoint(c0);
            result[1] = sb.toString();
            return result;
        }
        int length = 1;
        int nCodePoints = countCodePoints(input);
        for (int x = 1; x < nCodePoints; x++) length = length * (x + 1);
        String[] temp = new String[length];
        int[] combClass = new int[nCodePoints];
        for (int x = 0, i = 0; x < nCodePoints; x++) {
            int c = Character.codePointAt(input, i);
            combClass[x] = getClass(c);
            i += Character.charCount(c);
        }
        int index = 0;
        int len;
        loop: for (int x = 0, offset = 0; x < nCodePoints; x++, offset += len) {
            len = countChars(input, offset, 1);
            boolean skip = false;
            for (int y = x - 1; y >= 0; y--) {
                if (combClass[y] == combClass[x]) {
                    continue loop;
                }
            }
            StringBuilder sb = new StringBuilder(input);
            String otherChars = sb.delete(offset, offset + len).toString();
            String[] subResult = producePermutations(otherChars);
            String prefix = input.substring(offset, offset + len);
            for (int y = 0; y < subResult.length; y++) temp[index++] = prefix + subResult[y];
        }
        String[] result = new String[index];
        for (int x = 0; x < index; x++) result[x] = temp[x];
        return result;
    }
    
    private int getClass(int c) {
        return Normalizer.getClass(c);
    }
    
    private String composeOneStep(String input) {
        int len = countChars(input, 0, 2);
        String firstTwoCharacters = input.substring(0, len);
        String result = Normalizer.compose(firstTwoCharacters, false, 0);
        if (result.equals(firstTwoCharacters)) return null; else {
            String remainder = input.substring(len);
            return result + remainder;
        }
    }
    
    private void compile() {
        if (has(CANON_EQ) && !has(LITERAL)) {
            normalize();
        } else {
            normalizedPattern = pattern;
        }
        patternLength = normalizedPattern.length();
        temp = new int[patternLength + 2];
        boolean hasSupplementary = false;
        int c;
        int count = 0;
        for (int x = 0; x < patternLength; x += Character.charCount(c)) {
            c = normalizedPattern.codePointAt(x);
            if (isSupplementary(c)) {
                hasSupplementary = true;
            }
            temp[count++] = c;
        }
        patternLength = count;
        temp[patternLength] = 0;
        temp[patternLength + 1] = 0;
        buffer = new int[32];
        groupNodes = new Pattern$GroupHead[10];
        if (has(LITERAL)) {
            matchRoot = newSlice(temp, patternLength, hasSupplementary);
            matchRoot.next = lastAccept;
        } else {
            matchRoot = expr(lastAccept);
            if (patternLength != cursor) {
                if (peek() == ')') {
                    error("Unmatched closing \')\'");
                } else {
                    error("Unexpected internal error");
                }
            }
        }
        if (matchRoot instanceof Pattern$Slice) {
            root = Pattern$BnM.optimize(matchRoot);
            if (root == matchRoot) {
                root = hasSupplementary ? new Pattern$StartS(matchRoot) : new Pattern$Start(matchRoot);
            }
        } else if (matchRoot instanceof Pattern$Begin || matchRoot instanceof Pattern$First) {
            root = matchRoot;
        } else {
            root = hasSupplementary ? new Pattern$StartS(matchRoot) : new Pattern$Start(matchRoot);
        }
        temp = null;
        buffer = null;
        groupNodes = null;
        patternLength = 0;
        compiled = true;
    }
    
    private static void printObjectTree(Pattern$Node node) {
        while (node != null) {
            if (node instanceof Pattern$Prolog) {
                System.out.println(node);
                printObjectTree(((Pattern$Prolog)(Pattern$Prolog)node).loop);
                System.out.println("**** end contents prolog loop");
            } else if (node instanceof Pattern$Loop) {
                System.out.println(node);
                printObjectTree(((Pattern$Loop)(Pattern$Loop)node).body);
                System.out.println("**** end contents Loop body");
            } else if (node instanceof Pattern$Curly) {
                System.out.println(node);
                printObjectTree(((Pattern$Curly)(Pattern$Curly)node).atom);
                System.out.println("**** end contents Curly body");
            } else if (node instanceof Pattern$GroupCurly) {
                System.out.println(node);
                printObjectTree(((Pattern$GroupCurly)(Pattern$GroupCurly)node).atom);
                System.out.println("**** end contents GroupCurly body");
            } else if (node instanceof Pattern$GroupTail) {
                System.out.println(node);
                System.out.println("Tail next is " + node.next);
                return;
            } else {
                System.out.println(node);
            }
            node = node.next;
            if (node != null) System.out.println("->next:");
            if (node == Pattern.accept) {
                System.out.println("Accept Node");
                node = null;
            }
        }
    }
    {
    }
    
    private boolean has(int f) {
        return (flags & f) > 0;
    }
    
    private void accept(int ch, String s) {
        int testChar = temp[cursor++];
        if (has(COMMENTS)) testChar = parsePastWhitespace(testChar);
        if (ch != testChar) {
            error(s);
        }
    }
    
    private void mark(int c) {
        temp[patternLength] = c;
    }
    
    private int peek() {
        int ch = temp[cursor];
        if (has(COMMENTS)) ch = peekPastWhitespace(ch);
        return ch;
    }
    
    private int read() {
        int ch = temp[cursor++];
        if (has(COMMENTS)) ch = parsePastWhitespace(ch);
        return ch;
    }
    
    private int readEscaped() {
        int ch = temp[cursor++];
        return ch;
    }
    
    private int next() {
        int ch = temp[++cursor];
        if (has(COMMENTS)) ch = peekPastWhitespace(ch);
        return ch;
    }
    
    private int nextEscaped() {
        int ch = temp[++cursor];
        return ch;
    }
    
    private int peekPastWhitespace(int ch) {
        while (ASCII.isSpace(ch) || ch == '#') {
            while (ASCII.isSpace(ch)) ch = temp[++cursor];
            if (ch == '#') {
                ch = peekPastLine();
            }
        }
        return ch;
    }
    
    private int parsePastWhitespace(int ch) {
        while (ASCII.isSpace(ch) || ch == '#') {
            while (ASCII.isSpace(ch)) ch = temp[cursor++];
            if (ch == '#') ch = parsePastLine();
        }
        return ch;
    }
    
    private int parsePastLine() {
        int ch = temp[cursor++];
        while (ch != 0 && !isLineSeparator(ch)) ch = temp[cursor++];
        return ch;
    }
    
    private int peekPastLine() {
        int ch = temp[++cursor];
        while (ch != 0 && !isLineSeparator(ch)) ch = temp[++cursor];
        return ch;
    }
    
    private boolean isLineSeparator(int ch) {
        if (has(UNIX_LINES)) {
            return ch == '\n';
        } else {
            return (ch == '\n' || ch == '\r' || (ch | 1) == '\u2029' || ch == '\205');
        }
    }
    
    private int skip() {
        int i = cursor;
        int ch = temp[i + 1];
        cursor = i + 2;
        return ch;
    }
    
    private void unread() {
        cursor--;
    }
    
    private Pattern$Node error(String s) {
        throw new PatternSyntaxException(s, normalizedPattern, cursor - 1);
    }
    
    private boolean findSupplementary(int start, int end) {
        for (int i = start; i < end; i++) {
            if (isSupplementary(temp[i])) return true;
        }
        return false;
    }
    
    private static final boolean isSupplementary(int ch) {
        return ch >= Character.MIN_SUPPLEMENTARY_CODE_POINT || isSurrogate(ch);
    }
    
    private Pattern$Node expr(Pattern$Node end) {
        Pattern$Node prev = null;
        for (; ; ) {
            Pattern$Node node = sequence(end);
            if (prev == null) {
                prev = node;
            } else {
                prev = new Pattern$Branch(prev, node);
            }
            if (peek() != '|') {
                return prev;
            }
            next();
        }
    }
    
    private Pattern$Node sequence(Pattern$Node end) {
        Pattern$Node head = null;
        Pattern$Node tail = null;
        Pattern$Node node = null;
        int i;
        int j;
        int ch;
        LOOP: for (; ; ) {
            ch = peek();
            switch (ch) {
            case '(': 
                node = group0();
                if (node == null) continue;
                if (head == null) head = node; else tail.next = node;
                tail = root;
                continue;
            
            case '[': 
                node = clazz(true);
                break;
            
            case '\\': 
                ch = nextEscaped();
                if (ch == 'p' || ch == 'P') {
                    boolean comp = (ch == 'P');
                    boolean oneLetter = true;
                    ch = next();
                    if (ch != '{') {
                        unread();
                    } else {
                        oneLetter = false;
                    }
                    node = family(comp, oneLetter);
                } else {
                    unread();
                    node = atom();
                }
                break;
            
            case '^': 
                next();
                if (has(MULTILINE)) {
                    if (has(UNIX_LINES)) node = new Pattern$UnixCaret(); else node = new Pattern$Caret();
                } else {
                    node = new Pattern$Begin();
                }
                break;
            
            case '$': 
                next();
                if (has(UNIX_LINES)) node = new Pattern$UnixDollar(has(MULTILINE)); else node = new Pattern$Dollar(has(MULTILINE));
                break;
            
            case '.': 
                next();
                if (has(DOTALL)) {
                    node = new Pattern$All();
                } else {
                    if (has(UNIX_LINES)) node = new Pattern$UnixDot(); else {
                        node = new Pattern$Dot();
                    }
                }
                break;
            
            case '|': 
            
            case ')': 
                break LOOP;
            
            case ']': 
            
            case '}': 
                node = atom();
                break;
            
            case '?': 
            
            case '*': 
            
            case '+': 
                next();
                return error("Dangling meta character \'" + ((char)ch) + "\'");
            
            case 0: 
                if (cursor >= patternLength) {
                    break LOOP;
                }
            
            default: 
                node = atom();
                break;
            
            }
            node = closure(node);
            if (head == null) {
                head = tail = node;
            } else {
                tail.next = node;
                tail = node;
            }
        }
        if (head == null) {
            return end;
        }
        tail.next = end;
        return head;
    }
    
    private Pattern$Node atom() {
        int first = 0;
        int prev = -1;
        boolean hasSupplementary = false;
        int ch = peek();
        for (; ; ) {
            switch (ch) {
            case '*': 
            
            case '+': 
            
            case '?': 
            
            case '{': 
                if (first > 1) {
                    cursor = prev;
                    first--;
                }
                break;
            
            case '$': 
            
            case '.': 
            
            case '^': 
            
            case '(': 
            
            case '[': 
            
            case '|': 
            
            case ')': 
                break;
            
            case '\\': 
                ch = nextEscaped();
                if (ch == 'p' || ch == 'P') {
                    if (first > 0) {
                        unread();
                        break;
                    } else {
                        if (ch == 'p' || ch == 'P') {
                            boolean comp = (ch == 'P');
                            boolean oneLetter = true;
                            ch = next();
                            if (ch != '{') unread(); else oneLetter = false;
                            return family(comp, oneLetter);
                        }
                    }
                    break;
                }
                unread();
                prev = cursor;
                ch = escape(false, first == 0);
                if (ch >= 0) {
                    append(ch, first);
                    first++;
                    if (isSupplementary(ch)) {
                        hasSupplementary = true;
                    }
                    ch = peek();
                    continue;
                } else if (first == 0) {
                    return root;
                }
                cursor = prev;
                break;
            
            case 0: 
                if (cursor >= patternLength) {
                    break;
                }
            
            default: 
                prev = cursor;
                append(ch, first);
                first++;
                if (isSupplementary(ch)) {
                    hasSupplementary = true;
                }
                ch = next();
                continue;
            
            }
            break;
        }
        if (first == 1) {
            return newSingle(buffer[0]);
        } else {
            return newSlice(buffer, first, hasSupplementary);
        }
    }
    
    private void append(int ch, int len) {
        if (len >= buffer.length) {
            int[] tmp = new int[len + len];
            System.arraycopy(buffer, 0, tmp, 0, len);
            buffer = tmp;
        }
        buffer[len] = ch;
    }
    
    private Pattern$Node ref(int refNum) {
        boolean done = false;
        while (!done) {
            int ch = peek();
            switch (ch) {
            case '0': 
            
            case '1': 
            
            case '2': 
            
            case '3': 
            
            case '4': 
            
            case '5': 
            
            case '6': 
            
            case '7': 
            
            case '8': 
            
            case '9': 
                int newRefNum = (refNum * 10) + (ch - '0');
                if (capturingGroupCount - 1 < newRefNum) {
                    done = true;
                    break;
                }
                refNum = newRefNum;
                read();
                break;
            
            default: 
                done = true;
                break;
            
            }
        }
        if (has(CASE_INSENSITIVE) || has(UNICODE_CASE)) return new Pattern$CIBackRef(refNum); else return new Pattern$BackRef(refNum);
    }
    
    private int escape(boolean inclass, boolean create) {
        int ch = skip();
        switch (ch) {
        case '0': 
            return o();
        
        case '1': 
        
        case '2': 
        
        case '3': 
        
        case '4': 
        
        case '5': 
        
        case '6': 
        
        case '7': 
        
        case '8': 
        
        case '9': 
            if (inclass) break;
            if (capturingGroupCount < (ch - '0')) error("No such group yet exists at this point in the pattern");
            if (create) {
                root = ref((ch - '0'));
            }
            return -1;
        
        case 'A': 
            if (inclass) break;
            if (create) root = new Pattern$Begin();
            return -1;
        
        case 'B': 
            if (inclass) break;
            if (create) root = new Pattern$Bound(Pattern$Bound.NONE);
            return -1;
        
        case 'C': 
            break;
        
        case 'D': 
            if (create) root = new Pattern$NotCtype(ASCII.DIGIT);
            return -1;
        
        case 'E': 
        
        case 'F': 
            break;
        
        case 'G': 
            if (inclass) break;
            if (create) root = new Pattern$LastMatch();
            return -1;
        
        case 'H': 
        
        case 'I': 
        
        case 'J': 
        
        case 'K': 
        
        case 'L': 
        
        case 'M': 
        
        case 'N': 
        
        case 'O': 
        
        case 'P': 
            break;
        
        case 'Q': 
            if (create) {
                int i = cursor;
                int c;
                while ((c = readEscaped()) != 0) {
                    if (c == '\\') {
                        c = readEscaped();
                        if (c == 'E' || c == 0) break; else unread();
                    }
                }
                int j = cursor - 1;
                if (c == 'E') j--; else unread();
                boolean hasSupplementary = false;
                for (int x = i; x < j; x++) {
                    c = temp[x];
                    append(c, x - i);
                    if (isSupplementary(c)) {
                        hasSupplementary = true;
                    }
                }
                root = newSlice(buffer, j - i, hasSupplementary);
            }
            return -1;
        
        case 'R': 
            break;
        
        case 'S': 
            if (create) root = new Pattern$NotCtype(ASCII.SPACE);
            return -1;
        
        case 'T': 
        
        case 'U': 
        
        case 'V': 
            break;
        
        case 'W': 
            if (create) root = new Pattern$NotCtype(ASCII.WORD);
            return -1;
        
        case 'X': 
        
        case 'Y': 
            break;
        
        case 'Z': 
            if (inclass) break;
            if (create) {
                if (has(UNIX_LINES)) root = new Pattern$UnixDollar(false); else root = new Pattern$Dollar(false);
            }
            return -1;
        
        case 'a': 
            return '\007';
        
        case 'b': 
            if (inclass) break;
            if (create) root = new Pattern$Bound(Pattern$Bound.BOTH);
            return -1;
        
        case 'c': 
            return c();
        
        case 'd': 
            if (create) root = new Pattern$Ctype(ASCII.DIGIT);
            return -1;
        
        case 'e': 
            return '\033';
        
        case 'f': 
            return '\f';
        
        case 'g': 
        
        case 'h': 
        
        case 'i': 
        
        case 'j': 
        
        case 'k': 
        
        case 'l': 
        
        case 'm': 
            break;
        
        case 'n': 
            return '\n';
        
        case 'o': 
        
        case 'p': 
        
        case 'q': 
            break;
        
        case 'r': 
            return '\r';
        
        case 's': 
            if (create) root = new Pattern$Ctype(ASCII.SPACE);
            return -1;
        
        case 't': 
            return '\t';
        
        case 'u': 
            return u();
        
        case 'v': 
            return '\013';
        
        case 'w': 
            if (create) root = new Pattern$Ctype(ASCII.WORD);
            return -1;
        
        case 'x': 
            return x();
        
        case 'y': 
            break;
        
        case 'z': 
            if (inclass) break;
            if (create) root = new Pattern$End();
            return -1;
        
        default: 
            return ch;
        
        }
        error("Illegal/unsupported escape squence");
        return -2;
    }
    
    private Pattern$Node clazz(boolean consume) {
        Pattern$Node prev = null;
        Pattern$Node node = null;
        Pattern$BitClass bits = new Pattern$BitClass(false);
        boolean include = true;
        boolean firstInClass = true;
        int ch = next();
        for (; ; ) {
            switch (ch) {
            case '^': 
                if (firstInClass) {
                    if (temp[cursor - 1] != '[') break;
                    ch = next();
                    include = !include;
                    continue;
                } else {
                    break;
                }
            
            case '[': 
                firstInClass = false;
                node = clazz(true);
                if (prev == null) prev = node; else prev = new Pattern$Add(prev, node);
                ch = peek();
                continue;
            
            case '&': 
                firstInClass = false;
                ch = next();
                if (ch == '&') {
                    ch = next();
                    Pattern$Node rightNode = null;
                    while (ch != ']' && ch != '&') {
                        if (ch == '[') {
                            if (rightNode == null) rightNode = clazz(true); else rightNode = new Pattern$Add(rightNode, clazz(true));
                        } else {
                            unread();
                            rightNode = clazz(false);
                        }
                        ch = peek();
                    }
                    if (rightNode != null) node = rightNode;
                    if (prev == null) {
                        if (rightNode == null) return error("Bad class syntax"); else prev = rightNode;
                    } else {
                        prev = new Pattern$Both(prev, node);
                    }
                } else {
                    unread();
                    break;
                }
                continue;
            
            case 0: 
                firstInClass = false;
                if (cursor >= patternLength) return error("Unclosed character class");
                break;
            
            case ']': 
                firstInClass = false;
                if (prev != null) {
                    if (consume) next();
                    return prev;
                }
                break;
            
            default: 
                firstInClass = false;
                break;
            
            }
            node = range(bits);
            if (include) {
                if (prev == null) {
                    prev = node;
                } else {
                    if (prev != node) prev = new Pattern$Add(prev, node);
                }
            } else {
                if (prev == null) {
                    prev = node.dup(true);
                } else {
                    if (prev != node) prev = new Pattern$Sub(prev, node);
                }
            }
            ch = peek();
        }
    }
    
    private Pattern$Node range(Pattern$BitClass bits) {
        int ch = peek();
        if (ch == '\\') {
            ch = nextEscaped();
            if (ch == 'p' || ch == 'P') {
                boolean comp = (ch == 'P');
                boolean oneLetter = true;
                ch = next();
                if (ch != '{') unread(); else oneLetter = false;
                return family(comp, oneLetter);
            } else {
                unread();
                ch = escape(true, true);
                if (ch == -1) return root;
            }
        } else {
            ch = single();
        }
        if (ch >= 0) {
            if (peek() == '-') {
                int endRange = temp[cursor + 1];
                if (endRange == '[') {
                    if (ch < 256) return bits.add(ch, flags());
                    return newSingle(ch);
                }
                if (endRange != ']') {
                    next();
                    int m = single();
                    if (m < ch) return error("Illegal character range");
                    if (has(CASE_INSENSITIVE) || has(UNICODE_CASE)) return new Pattern$CIRange(ch, m); else return new Pattern$Range(ch, m);
                }
            }
            if (ch < 256) return bits.add(ch, flags());
            return newSingle(ch);
        }
        return error("Unexpected character \'" + ((char)ch) + "\'");
    }
    
    private int single() {
        int ch = peek();
        switch (ch) {
        case '\\': 
            return escape(true, false);
        
        default: 
            next();
            return ch;
        
        }
    }
    
    private Pattern$Node family(boolean not, boolean singleLetter) {
        next();
        String name;
        if (singleLetter) {
            int c = temp[cursor];
            if (!Character.isSupplementaryCodePoint(c)) {
                name = String.valueOf((char)c);
            } else {
                name = new String(temp, cursor, 1);
            }
            name = name.intern();
            read();
        } else {
            int i = cursor;
            mark('}');
            while (read() != '}') {
            }
            mark('\000');
            int j = cursor;
            if (j > patternLength) return error("Unclosed character family");
            if (i + 1 >= j) return error("Empty character family");
            name = new String(temp, i, j - i - 1).intern();
        }
        if (name.startsWith("In")) {
            name = name.substring(2, name.length()).intern();
            return retrieveFamilyNode(name, not);
        }
        if (name.startsWith("Is")) name = name.substring(2, name.length()).intern();
        return retrieveCategoryNode(name).dup(not);
    }
    
    private Pattern$Node retrieveFamilyNode(String name, boolean not) {
        if (name == null) {
            return familyError("", "Null character family.");
        }
        Pattern$Node n = null;
        try {
            Character$UnicodeBlock block = Character$UnicodeBlock.forName(name);
            n = new Pattern$UBlock(block, not);
        } catch (IllegalArgumentException iae) {
            return familyError(name, "Unknown character family {");
        }
        return n;
    }
    
    private Pattern$Node retrieveCategoryNode(String name) {
        Pattern$Node n = (Pattern$Node)(Pattern$Node)Pattern$categoryNames.cMap.get(name);
        if (n != null) return n;
        return familyError(name, "Unknown character category {");
    }
    
    private Pattern$Node familyError(String name, String type) {
        StringBuilder sb = new StringBuilder();
        sb.append(type);
        sb.append(name);
        sb.append("}");
        name = sb.toString();
        return error(name);
    }
    
    private Pattern$Node group0() {
        boolean capturingGroup = false;
        Pattern$Node head = null;
        Pattern$Node tail = null;
        int save = flags;
        root = null;
        int ch = next();
        if (ch == '?') {
            ch = skip();
            switch (ch) {
            case ':': 
                head = createGroup(true);
                tail = root;
                head.next = expr(tail);
                break;
            
            case '=': 
            
            case '!': 
                head = createGroup(true);
                tail = root;
                head.next = expr(tail);
                if (ch == '=') {
                    head = tail = new Pattern$Pos(head);
                } else {
                    head = tail = new Pattern$Neg(head);
                }
                break;
            
            case '>': 
                head = createGroup(true);
                tail = root;
                head.next = expr(tail);
                head = tail = new Pattern$Ques(head, INDEPENDENT);
                break;
            
            case '<': 
                ch = read();
                int start = cursor;
                head = createGroup(true);
                tail = root;
                head.next = expr(tail);
                Pattern$TreeInfo info = new Pattern$TreeInfo();
                head.study(info);
                if (info.maxValid == false) {
                    return error("Look-behind group does not have an obvious maximum length");
                }
                boolean hasSupplementary = findSupplementary(start, patternLength);
                if (ch == '=') {
                    head = tail = (hasSupplementary ? new Pattern$BehindS(head, info.maxLength, info.minLength) : new Pattern$Behind(head, info.maxLength, info.minLength));
                } else if (ch == '!') {
                    head = tail = (hasSupplementary ? new Pattern$NotBehindS(head, info.maxLength, info.minLength) : new Pattern$NotBehind(head, info.maxLength, info.minLength));
                } else {
                    error("Unknown look-behind group");
                }
                break;
            
            case '$': 
            
            case '@': 
                return error("Unknown group type");
            
            default: 
                unread();
                addFlag();
                ch = read();
                if (ch == ')') {
                    return null;
                }
                if (ch != ':') {
                    return error("Unknown inline modifier");
                }
                head = createGroup(true);
                tail = root;
                head.next = expr(tail);
                break;
            
            }
        } else {
            capturingGroup = true;
            head = createGroup(false);
            tail = root;
            head.next = expr(tail);
        }
        accept(')', "Unclosed group");
        flags = save;
        Pattern$Node node = closure(head);
        if (node == head) {
            root = tail;
            return node;
        }
        if (head == tail) {
            root = node;
            return node;
        }
        if (node instanceof Pattern$Ques) {
            Pattern$Ques ques = (Pattern$Ques)(Pattern$Ques)node;
            if (ques.type == POSSESSIVE) {
                root = node;
                return node;
            }
            tail.next = new Pattern$Dummy();
            tail = tail.next;
            if (ques.type == GREEDY) {
                head = new Pattern$Branch(head, tail);
            } else {
                head = new Pattern$Branch(tail, head);
            }
            root = tail;
            return head;
        } else if (node instanceof Pattern$Curly) {
            Pattern$Curly curly = (Pattern$Curly)(Pattern$Curly)node;
            if (curly.type == POSSESSIVE) {
                root = node;
                return node;
            }
            Pattern$TreeInfo info = new Pattern$TreeInfo();
            if (head.study(info)) {
                Pattern$GroupTail temp = (Pattern$GroupTail)(Pattern$GroupTail)tail;
                head = root = new Pattern$GroupCurly(head.next, curly.cmin, curly.cmax, curly.type, ((Pattern$GroupTail)(Pattern$GroupTail)tail).localIndex, ((Pattern$GroupTail)(Pattern$GroupTail)tail).groupIndex, capturingGroup);
                return head;
            } else {
                int temp = ((Pattern$GroupHead)(Pattern$GroupHead)head).localIndex;
                Pattern$Loop loop;
                if (curly.type == GREEDY) loop = new Pattern$Loop(this.localCount, temp); else loop = new Pattern$LazyLoop(this.localCount, temp);
                Pattern$Prolog prolog = new Pattern$Prolog(loop);
                this.localCount += 1;
                loop.cmin = curly.cmin;
                loop.cmax = curly.cmax;
                loop.body = head;
                tail.next = loop;
                root = loop;
                return prolog;
            }
        } else if (node instanceof Pattern$First) {
            root = node;
            return node;
        }
        return error("Internal logic error");
    }
    
    private Pattern$Node createGroup(boolean anonymous) {
        int localIndex = localCount++;
        int groupIndex = 0;
        if (!anonymous) groupIndex = capturingGroupCount++;
        Pattern$GroupHead head = new Pattern$GroupHead(localIndex);
        root = new Pattern$GroupTail(localIndex, groupIndex);
        if (!anonymous && groupIndex < 10) groupNodes[groupIndex] = head;
        return head;
    }
    
    private void addFlag() {
        int ch = peek();
        for (; ; ) {
            switch (ch) {
            case 'i': 
                flags |= CASE_INSENSITIVE;
                break;
            
            case 'm': 
                flags |= MULTILINE;
                break;
            
            case 's': 
                flags |= DOTALL;
                break;
            
            case 'd': 
                flags |= UNIX_LINES;
                break;
            
            case 'u': 
                flags |= UNICODE_CASE;
                break;
            
            case 'c': 
                flags |= CANON_EQ;
                break;
            
            case 'x': 
                flags |= COMMENTS;
                break;
            
            case '-': 
                ch = next();
                subFlag();
            
            default: 
                return;
            
            }
            ch = next();
        }
    }
    
    private void subFlag() {
        int ch = peek();
        for (; ; ) {
            switch (ch) {
            case 'i': 
                flags &= ~CASE_INSENSITIVE;
                break;
            
            case 'm': 
                flags &= ~MULTILINE;
                break;
            
            case 's': 
                flags &= ~DOTALL;
                break;
            
            case 'd': 
                flags &= ~UNIX_LINES;
                break;
            
            case 'u': 
                flags &= ~UNICODE_CASE;
                break;
            
            case 'c': 
                flags &= ~CANON_EQ;
                break;
            
            case 'x': 
                flags &= ~COMMENTS;
                break;
            
            default: 
                return;
            
            }
            ch = next();
        }
    }
    static final int MAX_REPS = 2147483647;
    static final int GREEDY = 0;
    static final int LAZY = 1;
    static final int POSSESSIVE = 2;
    static final int INDEPENDENT = 3;
    
    private Pattern$Node closure(Pattern$Node prev) {
        Pattern$Node atom;
        int ch = peek();
        switch (ch) {
        case '?': 
            ch = next();
            if (ch == '?') {
                next();
                return new Pattern$Ques(prev, LAZY);
            } else if (ch == '+') {
                next();
                return new Pattern$Ques(prev, POSSESSIVE);
            }
            return new Pattern$Ques(prev, GREEDY);
        
        case '*': 
            ch = next();
            if (ch == '?') {
                next();
                return new Pattern$Curly(prev, 0, MAX_REPS, LAZY);
            } else if (ch == '+') {
                next();
                return new Pattern$Curly(prev, 0, MAX_REPS, POSSESSIVE);
            }
            return new Pattern$Curly(prev, 0, MAX_REPS, GREEDY);
        
        case '+': 
            ch = next();
            if (ch == '?') {
                next();
                return new Pattern$Curly(prev, 1, MAX_REPS, LAZY);
            } else if (ch == '+') {
                next();
                return new Pattern$Curly(prev, 1, MAX_REPS, POSSESSIVE);
            }
            return new Pattern$Curly(prev, 1, MAX_REPS, GREEDY);
        
        case '{': 
            ch = temp[cursor + 1];
            if (ASCII.isDigit(ch)) {
                skip();
                int cmin = 0;
                do {
                    cmin = cmin * 10 + (ch - '0');
                }                 while (ASCII.isDigit(ch = read()));
                int cmax = cmin;
                if (ch == ',') {
                    ch = read();
                    cmax = MAX_REPS;
                    if (ch != '}') {
                        cmax = 0;
                        while (ASCII.isDigit(ch)) {
                            cmax = cmax * 10 + (ch - '0');
                            ch = read();
                        }
                    }
                }
                if (ch != '}') return error("Unclosed counted closure");
                if (((cmin) | (cmax) | (cmax - cmin)) < 0) return error("Illegal repetition range");
                Pattern$Curly curly;
                ch = peek();
                if (ch == '?') {
                    next();
                    curly = new Pattern$Curly(prev, cmin, cmax, LAZY);
                } else if (ch == '+') {
                    next();
                    curly = new Pattern$Curly(prev, cmin, cmax, POSSESSIVE);
                } else {
                    curly = new Pattern$Curly(prev, cmin, cmax, GREEDY);
                }
                return curly;
            } else {
                error("Illegal repetition");
            }
            return prev;
        
        default: 
            return prev;
        
        }
    }
    
    private int c() {
        if (cursor < patternLength) {
            return read() ^ 64;
        }
        error("Illegal control escape sequence");
        return -1;
    }
    
    private int o() {
        int n = read();
        if (((n - '0') | ('7' - n)) >= 0) {
            int m = read();
            if (((m - '0') | ('7' - m)) >= 0) {
                int o = read();
                if ((((o - '0') | ('7' - o)) >= 0) && (((n - '0') | ('3' - n)) >= 0)) {
                    return (n - '0') * 64 + (m - '0') * 8 + (o - '0');
                }
                unread();
                return (n - '0') * 8 + (m - '0');
            }
            unread();
            return (n - '0');
        }
        error("Illegal octal escape sequence");
        return -1;
    }
    
    private int x() {
        int n = read();
        if (ASCII.isHexDigit(n)) {
            int m = read();
            if (ASCII.isHexDigit(m)) {
                return ASCII.toDigit(n) * 16 + ASCII.toDigit(m);
            }
        }
        error("Illegal hexadecimal escape sequence");
        return -1;
    }
    
    private int u() {
        int n = 0;
        for (int i = 0; i < 4; i++) {
            int ch = read();
            if (!ASCII.isHexDigit(ch)) {
                error("Illegal Unicode escape sequence");
            }
            n = n * 16 + ASCII.toDigit(ch);
        }
        return n;
    }
    
    private static final boolean isSurrogate(int c) {
        return c >= Character.MIN_HIGH_SURROGATE && c <= Character.MAX_LOW_SURROGATE;
    }
    
    private static final int countChars(CharSequence seq, int index, int lengthInCodePoints) {
        if (lengthInCodePoints == 1 && !Character.isHighSurrogate(seq.charAt(index))) {
            if (!$assertionsDisabled && !(index >= 0 && index < seq.length())) throw new AssertionError();
            return 1;
        }
        int length = seq.length();
        int x = index;
        if (lengthInCodePoints >= 0) {
            if (!$assertionsDisabled && !(index >= 0 && index < length)) throw new AssertionError();
            for (int i = 0; x < length && i < lengthInCodePoints; i++) {
                if (Character.isHighSurrogate(seq.charAt(x++))) {
                    if (x < length && Character.isLowSurrogate(seq.charAt(x))) {
                        x++;
                    }
                }
            }
            return x - index;
        }
        if (!$assertionsDisabled && !(index >= 0 && index <= length)) throw new AssertionError();
        if (index == 0) {
            return 0;
        }
        int len = -lengthInCodePoints;
        for (int i = 0; x > 0 && i < len; i++) {
            if (Character.isLowSurrogate(seq.charAt(--x))) {
                if (x > 0 && Character.isHighSurrogate(seq.charAt(x - 1))) {
                    x--;
                }
            }
        }
        return index - x;
    }
    
    private static final int countCodePoints(CharSequence seq) {
        int length = seq.length();
        int n = 0;
        for (int i = 0; i < length; ) {
            n++;
            if (Character.isHighSurrogate(seq.charAt(i++))) {
                if (i < length && Character.isLowSurrogate(seq.charAt(i))) {
                    i++;
                }
            }
        }
        return n;
    }
    {
    }
    
    private Pattern$Node newSingle(int ch) {
        int f = flags;
        if ((f & (CASE_INSENSITIVE | UNICODE_CASE)) == 0) {
            return new Pattern$Single(ch);
        }
        if ((f & UNICODE_CASE) == 0) {
            return new Pattern$SingleA(ch);
        }
        return new Pattern$SingleU(ch);
    }
    
    private Pattern$Node newSlice(int[] buf, int count, boolean hasSupplementary) {
        int[] tmp = new int[count];
        int i = flags;
        if ((i & (CASE_INSENSITIVE | UNICODE_CASE)) == 0) {
            for (i = 0; i < count; i++) {
                tmp[i] = buf[i];
            }
            return hasSupplementary ? new Pattern$SliceS(tmp) : new Pattern$Slice(tmp);
        } else if ((i & UNICODE_CASE) == 0) {
            for (i = 0; i < count; i++) {
                tmp[i] = (char)ASCII.toLower(buf[i]);
            }
            return new Pattern$SliceA(tmp);
        } else {
            for (i = 0; i < count; i++) {
                int c = buf[i];
                c = Character.toUpperCase(c);
                c = Character.toLowerCase(c);
                tmp[i] = c;
            }
            return new Pattern$SliceU(tmp);
        }
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    private static boolean hasBaseCharacter(Matcher matcher, int i, CharSequence seq) {
        int start = (!matcher.transparentBounds) ? matcher.from : 0;
        for (int x = i; x >= start; x--) {
            int ch = Character.codePointAt(seq, x);
            if (Character.isLetterOrDigit(ch)) return true;
            if (Character.getType(ch) == Character.NON_SPACING_MARK) continue;
            return false;
        }
        return false;
    }
    {
    }
    {
    }
    {
    }
    static Pattern$Node accept = new Pattern$Node();
    static Pattern$Node lastAccept = new Pattern$LastNode();
    {
    }
}
