package java.lang;

public final class Character extends Object implements java.io.Serializable, Comparable {
    /*synthetic*/ static final boolean $assertionsDisabled = !Character.class.desiredAssertionStatus();
    public static final int MIN_RADIX = 2;
    public static final int MAX_RADIX = 36;
    public static final char MIN_VALUE = '\000';
    public static final char MAX_VALUE = '\uffff';
    public static final Class TYPE = Class.getPrimitiveClass("char");
    public static final byte UNASSIGNED = 0;
    public static final byte UPPERCASE_LETTER = 1;
    public static final byte LOWERCASE_LETTER = 2;
    public static final byte TITLECASE_LETTER = 3;
    public static final byte MODIFIER_LETTER = 4;
    public static final byte OTHER_LETTER = 5;
    public static final byte NON_SPACING_MARK = 6;
    public static final byte ENCLOSING_MARK = 7;
    public static final byte COMBINING_SPACING_MARK = 8;
    public static final byte DECIMAL_DIGIT_NUMBER = 9;
    public static final byte LETTER_NUMBER = 10;
    public static final byte OTHER_NUMBER = 11;
    public static final byte SPACE_SEPARATOR = 12;
    public static final byte LINE_SEPARATOR = 13;
    public static final byte PARAGRAPH_SEPARATOR = 14;
    public static final byte CONTROL = 15;
    public static final byte FORMAT = 16;
    public static final byte PRIVATE_USE = 18;
    public static final byte SURROGATE = 19;
    public static final byte DASH_PUNCTUATION = 20;
    public static final byte START_PUNCTUATION = 21;
    public static final byte END_PUNCTUATION = 22;
    public static final byte CONNECTOR_PUNCTUATION = 23;
    public static final byte OTHER_PUNCTUATION = 24;
    public static final byte MATH_SYMBOL = 25;
    public static final byte CURRENCY_SYMBOL = 26;
    public static final byte MODIFIER_SYMBOL = 27;
    public static final byte OTHER_SYMBOL = 28;
    public static final byte INITIAL_QUOTE_PUNCTUATION = 29;
    public static final byte FINAL_QUOTE_PUNCTUATION = 30;
    static final int ERROR = -1;
    public static final byte DIRECTIONALITY_UNDEFINED = -1;
    public static final byte DIRECTIONALITY_LEFT_TO_RIGHT = 0;
    public static final byte DIRECTIONALITY_RIGHT_TO_LEFT = 1;
    public static final byte DIRECTIONALITY_RIGHT_TO_LEFT_ARABIC = 2;
    public static final byte DIRECTIONALITY_EUROPEAN_NUMBER = 3;
    public static final byte DIRECTIONALITY_EUROPEAN_NUMBER_SEPARATOR = 4;
    public static final byte DIRECTIONALITY_EUROPEAN_NUMBER_TERMINATOR = 5;
    public static final byte DIRECTIONALITY_ARABIC_NUMBER = 6;
    public static final byte DIRECTIONALITY_COMMON_NUMBER_SEPARATOR = 7;
    public static final byte DIRECTIONALITY_NONSPACING_MARK = 8;
    public static final byte DIRECTIONALITY_BOUNDARY_NEUTRAL = 9;
    public static final byte DIRECTIONALITY_PARAGRAPH_SEPARATOR = 10;
    public static final byte DIRECTIONALITY_SEGMENT_SEPARATOR = 11;
    public static final byte DIRECTIONALITY_WHITESPACE = 12;
    public static final byte DIRECTIONALITY_OTHER_NEUTRALS = 13;
    public static final byte DIRECTIONALITY_LEFT_TO_RIGHT_EMBEDDING = 14;
    public static final byte DIRECTIONALITY_LEFT_TO_RIGHT_OVERRIDE = 15;
    public static final byte DIRECTIONALITY_RIGHT_TO_LEFT_EMBEDDING = 16;
    public static final byte DIRECTIONALITY_RIGHT_TO_LEFT_OVERRIDE = 17;
    public static final byte DIRECTIONALITY_POP_DIRECTIONAL_FORMAT = 18;
    public static final char MIN_HIGH_SURROGATE = '\ud800';
    public static final char MAX_HIGH_SURROGATE = '\udbff';
    public static final char MIN_LOW_SURROGATE = '\udc00';
    public static final char MAX_LOW_SURROGATE = '\udfff';
    public static final char MIN_SURROGATE = MIN_HIGH_SURROGATE;
    public static final char MAX_SURROGATE = MAX_LOW_SURROGATE;
    public static final int MIN_SUPPLEMENTARY_CODE_POINT = 65536;
    public static final int MIN_CODE_POINT = 0;
    public static final int MAX_CODE_POINT = 1114111;
    {
    }
    {
    }
    private final char value;
    private static final long serialVersionUID = 3786198910865385080L;
    
    public Character(char value) {
        
        this.value = value;
    }
    {
    }
    
    public static Character valueOf(char c) {
        if (c <= 127) {
            return Character$CharacterCache.cache[(int)c];
        }
        return new Character(c);
    }
    
    public char charValue() {
        return value;
    }
    
    public int hashCode() {
        return (int)value;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Character) {
            return value == ((Character)(Character)obj).charValue();
        }
        return false;
    }
    
    public String toString() {
        char[] buf = {value};
        return String.valueOf(buf);
    }
    
    public static String toString(char c) {
        return String.valueOf(c);
    }
    private static final int FAST_PATH_MAX = 255;
    
    private static int getPlane(int ch) {
        return (ch >>> 16);
    }
    
    public static boolean isValidCodePoint(int codePoint) {
        return codePoint >= MIN_CODE_POINT && codePoint <= MAX_CODE_POINT;
    }
    
    public static boolean isSupplementaryCodePoint(int codePoint) {
        return codePoint >= MIN_SUPPLEMENTARY_CODE_POINT && codePoint <= MAX_CODE_POINT;
    }
    
    public static boolean isHighSurrogate(char ch) {
        return ch >= MIN_HIGH_SURROGATE && ch <= MAX_HIGH_SURROGATE;
    }
    
    public static boolean isLowSurrogate(char ch) {
        return ch >= MIN_LOW_SURROGATE && ch <= MAX_LOW_SURROGATE;
    }
    
    public static boolean isSurrogatePair(char high, char low) {
        return isHighSurrogate(high) && isLowSurrogate(low);
    }
    
    public static int charCount(int codePoint) {
        return codePoint >= MIN_SUPPLEMENTARY_CODE_POINT ? 2 : 1;
    }
    
    public static int toCodePoint(char high, char low) {
        return ((high - MIN_HIGH_SURROGATE) << 10) + (low - MIN_LOW_SURROGATE) + MIN_SUPPLEMENTARY_CODE_POINT;
    }
    
    public static int codePointAt(CharSequence seq, int index) {
        char c1 = seq.charAt(index++);
        if (isHighSurrogate(c1)) {
            if (index < seq.length()) {
                char c2 = seq.charAt(index);
                if (isLowSurrogate(c2)) {
                    return toCodePoint(c1, c2);
                }
            }
        }
        return c1;
    }
    
    public static int codePointAt(char[] a, int index) {
        return codePointAtImpl(a, index, a.length);
    }
    
    public static int codePointAt(char[] a, int index, int limit) {
        if (index >= limit || limit < 0 || limit > a.length) {
            throw new IndexOutOfBoundsException();
        }
        return codePointAtImpl(a, index, limit);
    }
    
    static int codePointAtImpl(char[] a, int index, int limit) {
        char c1 = a[index++];
        if (isHighSurrogate(c1)) {
            if (index < limit) {
                char c2 = a[index];
                if (isLowSurrogate(c2)) {
                    return toCodePoint(c1, c2);
                }
            }
        }
        return c1;
    }
    
    public static int codePointBefore(CharSequence seq, int index) {
        char c2 = seq.charAt(--index);
        if (isLowSurrogate(c2)) {
            if (index > 0) {
                char c1 = seq.charAt(--index);
                if (isHighSurrogate(c1)) {
                    return toCodePoint(c1, c2);
                }
            }
        }
        return c2;
    }
    
    public static int codePointBefore(char[] a, int index) {
        return codePointBeforeImpl(a, index, 0);
    }
    
    public static int codePointBefore(char[] a, int index, int start) {
        if (index <= start || start < 0 || start >= a.length) {
            throw new IndexOutOfBoundsException();
        }
        return codePointBeforeImpl(a, index, start);
    }
    
    static int codePointBeforeImpl(char[] a, int index, int start) {
        char c2 = a[--index];
        if (isLowSurrogate(c2)) {
            if (index > start) {
                char c1 = a[--index];
                if (isHighSurrogate(c1)) {
                    return toCodePoint(c1, c2);
                }
            }
        }
        return c2;
    }
    
    public static int toChars(int codePoint, char[] dst, int dstIndex) {
        if (codePoint < 0 || codePoint > MAX_CODE_POINT) {
            throw new IllegalArgumentException();
        }
        if (codePoint < MIN_SUPPLEMENTARY_CODE_POINT) {
            dst[dstIndex] = (char)codePoint;
            return 1;
        }
        toSurrogates(codePoint, dst, dstIndex);
        return 2;
    }
    
    public static char[] toChars(int codePoint) {
        if (codePoint < 0 || codePoint > MAX_CODE_POINT) {
            throw new IllegalArgumentException();
        }
        if (codePoint < MIN_SUPPLEMENTARY_CODE_POINT) {
            return new char[]{(char)codePoint};
        }
        char[] result = new char[2];
        toSurrogates(codePoint, result, 0);
        return result;
    }
    
    static void toSurrogates(int codePoint, char[] dst, int index) {
        int offset = codePoint - MIN_SUPPLEMENTARY_CODE_POINT;
        dst[index + 1] = (char)((offset & 1023) + MIN_LOW_SURROGATE);
        dst[index] = (char)((offset >>> 10) + MIN_HIGH_SURROGATE);
    }
    
    public static int codePointCount(CharSequence seq, int beginIndex, int endIndex) {
        int length = seq.length();
        if (beginIndex < 0 || endIndex > length || beginIndex > endIndex) {
            throw new IndexOutOfBoundsException();
        }
        int n = 0;
        for (int i = beginIndex; i < endIndex; ) {
            n++;
            if (isHighSurrogate(seq.charAt(i++))) {
                if (i < endIndex && isLowSurrogate(seq.charAt(i))) {
                    i++;
                }
            }
        }
        return n;
    }
    
    public static int codePointCount(char[] a, int offset, int count) {
        if (count > a.length - offset || offset < 0 || count < 0) {
            throw new IndexOutOfBoundsException();
        }
        return codePointCountImpl(a, offset, count);
    }
    
    static int codePointCountImpl(char[] a, int offset, int count) {
        int endIndex = offset + count;
        int n = 0;
        for (int i = offset; i < endIndex; ) {
            n++;
            if (isHighSurrogate(a[i++])) {
                if (i < endIndex && isLowSurrogate(a[i])) {
                    i++;
                }
            }
        }
        return n;
    }
    
    public static int offsetByCodePoints(CharSequence seq, int index, int codePointOffset) {
        int length = seq.length();
        if (index < 0 || index > length) {
            throw new IndexOutOfBoundsException();
        }
        int x = index;
        if (codePointOffset >= 0) {
            int i;
            for (i = 0; x < length && i < codePointOffset; i++) {
                if (isHighSurrogate(seq.charAt(x++))) {
                    if (x < length && isLowSurrogate(seq.charAt(x))) {
                        x++;
                    }
                }
            }
            if (i < codePointOffset) {
                throw new IndexOutOfBoundsException();
            }
        } else {
            int i;
            for (i = codePointOffset; x > 0 && i < 0; i++) {
                if (isLowSurrogate(seq.charAt(--x))) {
                    if (x > 0 && isHighSurrogate(seq.charAt(x - 1))) {
                        x--;
                    }
                }
            }
            if (i < 0) {
                throw new IndexOutOfBoundsException();
            }
        }
        return x;
    }
    
    public static int offsetByCodePoints(char[] a, int start, int count, int index, int codePointOffset) {
        if (count > a.length - start || start < 0 || count < 0 || index < start || index > start + count) {
            throw new IndexOutOfBoundsException();
        }
        return offsetByCodePointsImpl(a, start, count, index, codePointOffset);
    }
    
    static int offsetByCodePointsImpl(char[] a, int start, int count, int index, int codePointOffset) {
        int x = index;
        if (codePointOffset >= 0) {
            int limit = start + count;
            int i;
            for (i = 0; x < limit && i < codePointOffset; i++) {
                if (isHighSurrogate(a[x++])) {
                    if (x < limit && isLowSurrogate(a[x])) {
                        x++;
                    }
                }
            }
            if (i < codePointOffset) {
                throw new IndexOutOfBoundsException();
            }
        } else {
            int i;
            for (i = codePointOffset; x > start && i < 0; i++) {
                if (isLowSurrogate(a[--x])) {
                    if (x > start && isHighSurrogate(a[x - 1])) {
                        x--;
                    }
                }
            }
            if (i < 0) {
                throw new IndexOutOfBoundsException();
            }
        }
        return x;
    }
    
    public static boolean isLowerCase(char ch) {
        return isLowerCase((int)ch);
    }
    
    public static boolean isLowerCase(int codePoint) {
        boolean bLowerCase = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bLowerCase = CharacterDataLatin1.isLowerCase(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bLowerCase = CharacterData00.isLowerCase(codePoint);
                break;
            
            case (1): 
                bLowerCase = CharacterData01.isLowerCase(codePoint);
                break;
            
            case (2): 
                bLowerCase = CharacterData02.isLowerCase(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bLowerCase = CharacterDataUndefined.isLowerCase(codePoint);
                break;
            
            case (14): 
                bLowerCase = CharacterData0E.isLowerCase(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bLowerCase = CharacterDataPrivateUse.isLowerCase(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bLowerCase;
    }
    
    public static boolean isUpperCase(char ch) {
        return isUpperCase((int)ch);
    }
    
    public static boolean isUpperCase(int codePoint) {
        boolean bUpperCase = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bUpperCase = CharacterDataLatin1.isUpperCase(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bUpperCase = CharacterData00.isUpperCase(codePoint);
                break;
            
            case (1): 
                bUpperCase = CharacterData01.isUpperCase(codePoint);
                break;
            
            case (2): 
                bUpperCase = CharacterData02.isUpperCase(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bUpperCase = CharacterDataUndefined.isUpperCase(codePoint);
                break;
            
            case (14): 
                bUpperCase = CharacterData0E.isUpperCase(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bUpperCase = CharacterDataPrivateUse.isUpperCase(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bUpperCase;
    }
    
    public static boolean isTitleCase(char ch) {
        return isTitleCase((int)ch);
    }
    
    public static boolean isTitleCase(int codePoint) {
        boolean bTitleCase = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bTitleCase = CharacterDataLatin1.isTitleCase(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bTitleCase = CharacterData00.isTitleCase(codePoint);
                break;
            
            case (1): 
                bTitleCase = CharacterData01.isTitleCase(codePoint);
                break;
            
            case (2): 
                bTitleCase = CharacterData02.isTitleCase(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bTitleCase = CharacterDataUndefined.isTitleCase(codePoint);
                break;
            
            case (14): 
                bTitleCase = CharacterData0E.isTitleCase(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bTitleCase = CharacterDataPrivateUse.isTitleCase(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bTitleCase;
    }
    
    public static boolean isDigit(char ch) {
        return isDigit((int)ch);
    }
    
    public static boolean isDigit(int codePoint) {
        boolean bDigit = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bDigit = CharacterDataLatin1.isDigit(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bDigit = CharacterData00.isDigit(codePoint);
                break;
            
            case (1): 
                bDigit = CharacterData01.isDigit(codePoint);
                break;
            
            case (2): 
                bDigit = CharacterData02.isDigit(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bDigit = CharacterDataUndefined.isDigit(codePoint);
                break;
            
            case (14): 
                bDigit = CharacterData0E.isDigit(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bDigit = CharacterDataPrivateUse.isDigit(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bDigit;
    }
    
    public static boolean isDefined(char ch) {
        return isDefined((int)ch);
    }
    
    public static boolean isDefined(int codePoint) {
        boolean bDefined = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bDefined = CharacterDataLatin1.isDefined(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bDefined = CharacterData00.isDefined(codePoint);
                break;
            
            case (1): 
                bDefined = CharacterData01.isDefined(codePoint);
                break;
            
            case (2): 
                bDefined = CharacterData02.isDefined(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bDefined = CharacterDataUndefined.isDefined(codePoint);
                break;
            
            case (14): 
                bDefined = CharacterData0E.isDefined(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bDefined = CharacterDataPrivateUse.isDefined(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bDefined;
    }
    
    public static boolean isLetter(char ch) {
        return isLetter((int)ch);
    }
    
    public static boolean isLetter(int codePoint) {
        boolean bLetter = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bLetter = CharacterDataLatin1.isLetter(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bLetter = CharacterData00.isLetter(codePoint);
                break;
            
            case (1): 
                bLetter = CharacterData01.isLetter(codePoint);
                break;
            
            case (2): 
                bLetter = CharacterData02.isLetter(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bLetter = CharacterDataUndefined.isLetter(codePoint);
                break;
            
            case (14): 
                bLetter = CharacterData0E.isLetter(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bLetter = CharacterDataPrivateUse.isLetter(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bLetter;
    }
    
    public static boolean isLetterOrDigit(char ch) {
        return isLetterOrDigit((int)ch);
    }
    
    public static boolean isLetterOrDigit(int codePoint) {
        boolean bLetterOrDigit = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bLetterOrDigit = CharacterDataLatin1.isLetterOrDigit(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bLetterOrDigit = CharacterData00.isLetterOrDigit(codePoint);
                break;
            
            case (1): 
                bLetterOrDigit = CharacterData01.isLetterOrDigit(codePoint);
                break;
            
            case (2): 
                bLetterOrDigit = CharacterData02.isLetterOrDigit(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bLetterOrDigit = CharacterDataUndefined.isLetterOrDigit(codePoint);
                break;
            
            case (14): 
                bLetterOrDigit = CharacterData0E.isLetterOrDigit(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bLetterOrDigit = CharacterDataPrivateUse.isLetterOrDigit(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bLetterOrDigit;
    }
    
    
    public static boolean isJavaLetter(char ch) {
        return isJavaIdentifierStart(ch);
    }
    
    
    public static boolean isJavaLetterOrDigit(char ch) {
        return isJavaIdentifierPart(ch);
    }
    
    public static boolean isJavaIdentifierStart(char ch) {
        return isJavaIdentifierStart((int)ch);
    }
    
    public static boolean isJavaIdentifierStart(int codePoint) {
        boolean bJavaStart = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bJavaStart = CharacterDataLatin1.isJavaIdentifierStart(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bJavaStart = CharacterData00.isJavaIdentifierStart(codePoint);
                break;
            
            case (1): 
                bJavaStart = CharacterData01.isJavaIdentifierStart(codePoint);
                break;
            
            case (2): 
                bJavaStart = CharacterData02.isJavaIdentifierStart(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bJavaStart = CharacterDataUndefined.isJavaIdentifierStart(codePoint);
                break;
            
            case (14): 
                bJavaStart = CharacterData0E.isJavaIdentifierStart(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bJavaStart = CharacterDataPrivateUse.isJavaIdentifierStart(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bJavaStart;
    }
    
    public static boolean isJavaIdentifierPart(char ch) {
        return isJavaIdentifierPart((int)ch);
    }
    
    public static boolean isJavaIdentifierPart(int codePoint) {
        boolean bJavaPart = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bJavaPart = CharacterDataLatin1.isJavaIdentifierPart(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bJavaPart = CharacterData00.isJavaIdentifierPart(codePoint);
                break;
            
            case (1): 
                bJavaPart = CharacterData01.isJavaIdentifierPart(codePoint);
                break;
            
            case (2): 
                bJavaPart = CharacterData02.isJavaIdentifierPart(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bJavaPart = CharacterDataUndefined.isJavaIdentifierPart(codePoint);
                break;
            
            case (14): 
                bJavaPart = CharacterData0E.isJavaIdentifierPart(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bJavaPart = CharacterDataPrivateUse.isJavaIdentifierPart(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bJavaPart;
    }
    
    public static boolean isUnicodeIdentifierStart(char ch) {
        return isUnicodeIdentifierStart((int)ch);
    }
    
    public static boolean isUnicodeIdentifierStart(int codePoint) {
        boolean bUnicodeStart = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bUnicodeStart = CharacterDataLatin1.isUnicodeIdentifierStart(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bUnicodeStart = CharacterData00.isUnicodeIdentifierStart(codePoint);
                break;
            
            case (1): 
                bUnicodeStart = CharacterData01.isUnicodeIdentifierStart(codePoint);
                break;
            
            case (2): 
                bUnicodeStart = CharacterData02.isUnicodeIdentifierStart(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bUnicodeStart = CharacterDataUndefined.isUnicodeIdentifierStart(codePoint);
                break;
            
            case (14): 
                bUnicodeStart = CharacterData0E.isUnicodeIdentifierStart(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bUnicodeStart = CharacterDataPrivateUse.isUnicodeIdentifierStart(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bUnicodeStart;
    }
    
    public static boolean isUnicodeIdentifierPart(char ch) {
        return isUnicodeIdentifierPart((int)ch);
    }
    
    public static boolean isUnicodeIdentifierPart(int codePoint) {
        boolean bUnicodePart = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bUnicodePart = CharacterDataLatin1.isUnicodeIdentifierPart(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bUnicodePart = CharacterData00.isUnicodeIdentifierPart(codePoint);
                break;
            
            case (1): 
                bUnicodePart = CharacterData01.isUnicodeIdentifierPart(codePoint);
                break;
            
            case (2): 
                bUnicodePart = CharacterData02.isUnicodeIdentifierPart(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bUnicodePart = CharacterDataUndefined.isUnicodeIdentifierPart(codePoint);
                break;
            
            case (14): 
                bUnicodePart = CharacterData0E.isUnicodeIdentifierPart(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bUnicodePart = CharacterDataPrivateUse.isUnicodeIdentifierPart(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bUnicodePart;
    }
    
    public static boolean isIdentifierIgnorable(char ch) {
        return isIdentifierIgnorable((int)ch);
    }
    
    public static boolean isIdentifierIgnorable(int codePoint) {
        boolean bIdentifierIgnorable = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bIdentifierIgnorable = CharacterDataLatin1.isIdentifierIgnorable(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bIdentifierIgnorable = CharacterData00.isIdentifierIgnorable(codePoint);
                break;
            
            case (1): 
                bIdentifierIgnorable = CharacterData01.isIdentifierIgnorable(codePoint);
                break;
            
            case (2): 
                bIdentifierIgnorable = CharacterData02.isIdentifierIgnorable(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bIdentifierIgnorable = CharacterDataUndefined.isIdentifierIgnorable(codePoint);
                break;
            
            case (14): 
                bIdentifierIgnorable = CharacterData0E.isIdentifierIgnorable(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bIdentifierIgnorable = CharacterDataPrivateUse.isIdentifierIgnorable(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bIdentifierIgnorable;
    }
    
    public static char toLowerCase(char ch) {
        return (char)toLowerCase((int)ch);
    }
    
    public static int toLowerCase(int codePoint) {
        int lowerCase = codePoint;
        int plane = 0;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            lowerCase = CharacterDataLatin1.toLowerCase(codePoint);
        } else {
            plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                lowerCase = CharacterData00.toLowerCase(codePoint);
                break;
            
            case (1): 
                lowerCase = CharacterData01.toLowerCase(codePoint);
                break;
            
            case (2): 
                lowerCase = CharacterData02.toLowerCase(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                lowerCase = CharacterDataUndefined.toLowerCase(codePoint);
                break;
            
            case (14): 
                lowerCase = CharacterData0E.toLowerCase(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                lowerCase = CharacterDataPrivateUse.toLowerCase(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return lowerCase;
    }
    
    public static char toUpperCase(char ch) {
        return (char)toUpperCase((int)ch);
    }
    
    public static int toUpperCase(int codePoint) {
        int upperCase = codePoint;
        int plane = 0;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            upperCase = CharacterDataLatin1.toUpperCase(codePoint);
        } else {
            plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                upperCase = CharacterData00.toUpperCase(codePoint);
                break;
            
            case (1): 
                upperCase = CharacterData01.toUpperCase(codePoint);
                break;
            
            case (2): 
                upperCase = CharacterData02.toUpperCase(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                upperCase = CharacterDataUndefined.toUpperCase(codePoint);
                break;
            
            case (14): 
                upperCase = CharacterData0E.toUpperCase(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                upperCase = CharacterDataPrivateUse.toUpperCase(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return upperCase;
    }
    
    public static char toTitleCase(char ch) {
        return (char)toTitleCase((int)ch);
    }
    
    public static int toTitleCase(int codePoint) {
        int titleCase = codePoint;
        int plane = 0;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            titleCase = CharacterDataLatin1.toTitleCase(codePoint);
        } else {
            plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                titleCase = CharacterData00.toTitleCase(codePoint);
                break;
            
            case (1): 
                titleCase = CharacterData01.toTitleCase(codePoint);
                break;
            
            case (2): 
                titleCase = CharacterData02.toTitleCase(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                titleCase = CharacterDataUndefined.toTitleCase(codePoint);
                break;
            
            case (14): 
                titleCase = CharacterData0E.toTitleCase(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                titleCase = CharacterDataPrivateUse.toTitleCase(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return titleCase;
    }
    
    public static int digit(char ch, int radix) {
        return digit((int)ch, radix);
    }
    
    public static int digit(int codePoint, int radix) {
        int digit = -1;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            digit = CharacterDataLatin1.digit(codePoint, radix);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                digit = CharacterData00.digit(codePoint, radix);
                break;
            
            case (1): 
                digit = CharacterData01.digit(codePoint, radix);
                break;
            
            case (2): 
                digit = CharacterData02.digit(codePoint, radix);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                digit = CharacterDataUndefined.digit(codePoint, radix);
                break;
            
            case (14): 
                digit = CharacterData0E.digit(codePoint, radix);
                break;
            
            case (15): 
            
            case (16): 
                digit = CharacterDataPrivateUse.digit(codePoint, radix);
                break;
            
            default: 
                break;
            
            }
        }
        return digit;
    }
    
    public static int getNumericValue(char ch) {
        return getNumericValue((int)ch);
    }
    
    public static int getNumericValue(int codePoint) {
        int numericValue = -1;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            numericValue = CharacterDataLatin1.getNumericValue(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                numericValue = CharacterData00.getNumericValue(codePoint);
                break;
            
            case (1): 
                numericValue = CharacterData01.getNumericValue(codePoint);
                break;
            
            case (2): 
                numericValue = CharacterData02.getNumericValue(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                numericValue = CharacterDataUndefined.getNumericValue(codePoint);
                break;
            
            case (14): 
                numericValue = CharacterData0E.getNumericValue(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                numericValue = CharacterDataPrivateUse.getNumericValue(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return numericValue;
    }
    
    
    public static boolean isSpace(char ch) {
        return (ch <= 32) && (((((1L << 9) | (1L << 10) | (1L << 12) | (1L << 13) | (1L << 32)) >> ch) & 1L) != 0);
    }
    
    public static boolean isSpaceChar(char ch) {
        return isSpaceChar((int)ch);
    }
    
    public static boolean isSpaceChar(int codePoint) {
        boolean bSpaceChar = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bSpaceChar = CharacterDataLatin1.isSpaceChar(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bSpaceChar = CharacterData00.isSpaceChar(codePoint);
                break;
            
            case (1): 
                bSpaceChar = CharacterData01.isSpaceChar(codePoint);
                break;
            
            case (2): 
                bSpaceChar = CharacterData02.isSpaceChar(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bSpaceChar = CharacterDataUndefined.isSpaceChar(codePoint);
                break;
            
            case (14): 
                bSpaceChar = CharacterData0E.isSpaceChar(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bSpaceChar = CharacterDataPrivateUse.isSpaceChar(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bSpaceChar;
    }
    
    public static boolean isWhitespace(char ch) {
        return isWhitespace((int)ch);
    }
    
    public static boolean isWhitespace(int codePoint) {
        boolean bWhiteSpace = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bWhiteSpace = CharacterDataLatin1.isWhitespace(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bWhiteSpace = CharacterData00.isWhitespace(codePoint);
                break;
            
            case (1): 
                bWhiteSpace = CharacterData01.isWhitespace(codePoint);
                break;
            
            case (2): 
                bWhiteSpace = CharacterData02.isWhitespace(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bWhiteSpace = CharacterDataUndefined.isWhitespace(codePoint);
                break;
            
            case (14): 
                bWhiteSpace = CharacterData0E.isWhitespace(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bWhiteSpace = CharacterDataPrivateUse.isWhitespace(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bWhiteSpace;
    }
    
    public static boolean isISOControl(char ch) {
        return isISOControl((int)ch);
    }
    
    public static boolean isISOControl(int codePoint) {
        return (codePoint >= 0 && codePoint <= 31) || (codePoint >= 127 && codePoint <= 159);
    }
    
    public static int getType(char ch) {
        return getType((int)ch);
    }
    
    public static int getType(int codePoint) {
        int type = Character.UNASSIGNED;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            type = CharacterDataLatin1.getType(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                type = CharacterData00.getType(codePoint);
                break;
            
            case (1): 
                type = CharacterData01.getType(codePoint);
                break;
            
            case (2): 
                type = CharacterData02.getType(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                type = CharacterDataUndefined.getType(codePoint);
                break;
            
            case (14): 
                type = CharacterData0E.getType(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                type = CharacterDataPrivateUse.getType(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return type;
    }
    
    public static char forDigit(int digit, int radix) {
        if ((digit >= radix) || (digit < 0)) {
            return '\000';
        }
        if ((radix < Character.MIN_RADIX) || (radix > Character.MAX_RADIX)) {
            return '\000';
        }
        if (digit < 10) {
            return (char)('0' + digit);
        }
        return (char)('a' - 10 + digit);
    }
    
    public static byte getDirectionality(char ch) {
        return getDirectionality((int)ch);
    }
    
    public static byte getDirectionality(int codePoint) {
        byte directionality = Character.DIRECTIONALITY_UNDEFINED;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            directionality = CharacterDataLatin1.getDirectionality(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                directionality = CharacterData00.getDirectionality(codePoint);
                break;
            
            case (1): 
                directionality = CharacterData01.getDirectionality(codePoint);
                break;
            
            case (2): 
                directionality = CharacterData02.getDirectionality(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                directionality = CharacterDataUndefined.getDirectionality(codePoint);
                break;
            
            case (14): 
                directionality = CharacterData0E.getDirectionality(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                directionality = CharacterDataPrivateUse.getDirectionality(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return directionality;
    }
    
    public static boolean isMirrored(char ch) {
        return isMirrored((int)ch);
    }
    
    public static boolean isMirrored(int codePoint) {
        boolean bMirrored = false;
        if (codePoint >= MIN_CODE_POINT && codePoint <= FAST_PATH_MAX) {
            bMirrored = CharacterDataLatin1.isMirrored(codePoint);
        } else {
            int plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                bMirrored = CharacterData00.isMirrored(codePoint);
                break;
            
            case (1): 
                bMirrored = CharacterData01.isMirrored(codePoint);
                break;
            
            case (2): 
                bMirrored = CharacterData02.isMirrored(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                bMirrored = CharacterDataUndefined.isMirrored(codePoint);
                break;
            
            case (14): 
                bMirrored = CharacterData0E.isMirrored(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                bMirrored = CharacterDataPrivateUse.isMirrored(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return bMirrored;
    }
    
    public int compareTo(Character anotherCharacter) {
        return this.value - anotherCharacter.value;
    }
    
    static int toUpperCaseEx(int codePoint) {
        int upperCase = codePoint;
        int plane = 0;
        if (!$assertionsDisabled && !isValidCodePoint(codePoint)) throw new AssertionError();
        if (codePoint <= FAST_PATH_MAX) {
            upperCase = CharacterDataLatin1.toUpperCaseEx(codePoint);
        } else {
            plane = getPlane(codePoint);
            switch (plane) {
            case (0): 
                upperCase = CharacterData00.toUpperCaseEx(codePoint);
                break;
            
            case (1): 
                upperCase = CharacterData01.toUpperCase(codePoint);
                break;
            
            case (2): 
                upperCase = CharacterData02.toUpperCase(codePoint);
                break;
            
            case (3): 
            
            case (4): 
            
            case (5): 
            
            case (6): 
            
            case (7): 
            
            case (8): 
            
            case (9): 
            
            case (10): 
            
            case (11): 
            
            case (12): 
            
            case (13): 
                upperCase = CharacterDataUndefined.toUpperCase(codePoint);
                break;
            
            case (14): 
                upperCase = CharacterData0E.toUpperCase(codePoint);
                break;
            
            case (15): 
            
            case (16): 
                upperCase = CharacterDataPrivateUse.toUpperCase(codePoint);
                break;
            
            default: 
                break;
            
            }
        }
        return upperCase;
    }
    
    static char[] toUpperCaseCharArray(int codePoint) {
        char[] upperCase = null;
        if (!$assertionsDisabled && !(isValidCodePoint(codePoint) && !isSupplementaryCodePoint(codePoint))) throw new AssertionError();
        if (codePoint <= FAST_PATH_MAX) {
            upperCase = CharacterDataLatin1.toUpperCaseCharArray(codePoint);
        } else {
            upperCase = CharacterData00.toUpperCaseCharArray(codePoint);
        }
        return upperCase;
    }
    public static final int SIZE = 16;
    
    public static char reverseBytes(char ch) {
        return (char)(((ch & 65280) >> 8) | (ch << 8));
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Character)x0);
    }
}
