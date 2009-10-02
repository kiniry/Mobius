package java.lang;

class CharacterDataLatin1 {
    /*synthetic*/ static final boolean $assertionsDisabled = !CharacterDataLatin1.class.desiredAssertionStatus();
    
    CharacterDataLatin1() {
        
    }
    
    static int getProperties(int ch) {
        char offset = (char)ch;
        int props = A[offset];
        return props;
    }
    
    static int getType(int ch) {
        int props = getProperties(ch);
        return (props & 31);
    }
    
    static boolean isLowerCase(int ch) {
        int type = getType(ch);
        return (type == Character.LOWERCASE_LETTER);
    }
    
    static boolean isUpperCase(int ch) {
        int type = getType(ch);
        return (type == Character.UPPERCASE_LETTER);
    }
    
    static boolean isTitleCase(int ch) {
        return false;
    }
    
    static boolean isDigit(int ch) {
        int type = getType(ch);
        return (type == Character.DECIMAL_DIGIT_NUMBER);
    }
    
    static boolean isDefined(int ch) {
        int type = getType(ch);
        return (type != Character.UNASSIGNED);
    }
    
    static boolean isLetter(int ch) {
        int type = getType(ch);
        return (((((1 << Character.UPPERCASE_LETTER) | (1 << Character.LOWERCASE_LETTER) | (1 << Character.TITLECASE_LETTER) | (1 << Character.MODIFIER_LETTER) | (1 << Character.OTHER_LETTER)) >> type) & 1) != 0);
    }
    
    static boolean isLetterOrDigit(int ch) {
        int type = getType(ch);
        return (((((1 << Character.UPPERCASE_LETTER) | (1 << Character.LOWERCASE_LETTER) | (1 << Character.TITLECASE_LETTER) | (1 << Character.MODIFIER_LETTER) | (1 << Character.OTHER_LETTER) | (1 << Character.DECIMAL_DIGIT_NUMBER)) >> type) & 1) != 0);
    }
    
    static boolean isSpaceChar(int ch) {
        int type = getType(ch);
        return (((((1 << Character.SPACE_SEPARATOR) | (1 << Character.LINE_SEPARATOR) | (1 << Character.PARAGRAPH_SEPARATOR)) >> type) & 1) != 0);
    }
    
    static boolean isJavaIdentifierStart(int ch) {
        int props = getProperties(ch);
        return ((props & 28672) >= 20480);
    }
    
    static boolean isJavaIdentifierPart(int ch) {
        int props = getProperties(ch);
        return ((props & 12288) != 0);
    }
    
    static boolean isUnicodeIdentifierStart(int ch) {
        int props = getProperties(ch);
        return ((props & 28672) == 28672);
    }
    
    static boolean isUnicodeIdentifierPart(int ch) {
        int props = getProperties(ch);
        return ((props & 4096) != 0);
    }
    
    static boolean isIdentifierIgnorable(int ch) {
        int props = getProperties(ch);
        return ((props & 28672) == 4096);
    }
    
    static int toLowerCase(int ch) {
        int mapChar = ch;
        int val = getProperties(ch);
        if (((val & 131072) != 0) && ((val & 133955584) != 133955584)) {
            int offset = val << 5 >> (5 + 18);
            mapChar = ch + offset;
        }
        return mapChar;
    }
    
    static int toUpperCase(int ch) {
        int mapChar = ch;
        int val = getProperties(ch);
        if ((val & 65536) != 0) {
            if ((val & 133955584) != 133955584) {
                int offset = val << 5 >> (5 + 18);
                mapChar = ch - offset;
            } else if (ch == 181) {
                mapChar = 924;
            }
        }
        return mapChar;
    }
    
    static int toTitleCase(int ch) {
        return toUpperCase(ch);
    }
    
    static int digit(int ch, int radix) {
        int value = -1;
        if (radix >= Character.MIN_RADIX && radix <= Character.MAX_RADIX) {
            int val = getProperties(ch);
            int kind = val & 31;
            if (kind == Character.DECIMAL_DIGIT_NUMBER) {
                value = ch + ((val & 992) >> 5) & 31;
            } else if ((val & 3072) == 3072) {
                value = (ch + ((val & 992) >> 5) & 31) + 10;
            }
        }
        return (value < radix) ? value : -1;
    }
    
    static int getNumericValue(int ch) {
        int val = getProperties(ch);
        int retval = -1;
        switch (val & 3072) {
        default: 
        
        case (0): 
            retval = -1;
            break;
        
        case (1024): 
            retval = ch + ((val & 992) >> 5) & 31;
            break;
        
        case (2048): 
            retval = -2;
            break;
        
        case (3072): 
            retval = (ch + ((val & 992) >> 5) & 31) + 10;
            break;
        
        }
        return retval;
    }
    
    static boolean isWhitespace(int ch) {
        int props = getProperties(ch);
        return ((props & 28672) == 16384);
    }
    
    static byte getDirectionality(int ch) {
        int val = getProperties(ch);
        byte directionality = (byte)((val & 2013265920) >> 27);
        if (directionality == 15) {
            directionality = -1;
        }
        return directionality;
    }
    
    static boolean isMirrored(int ch) {
        int props = getProperties(ch);
        return ((props & -2147483648) != 0);
    }
    
    static int toUpperCaseEx(int ch) {
        int mapChar = ch;
        int val = getProperties(ch);
        if ((val & 65536) != 0) {
            if ((val & 133955584) != 133955584) {
                int offset = val << 5 >> (5 + 18);
                mapChar = ch - offset;
            } else {
                switch (ch) {
                case 181: 
                    mapChar = 924;
                    break;
                
                default: 
                    mapChar = Character.ERROR;
                    break;
                
                }
            }
        }
        return mapChar;
    }
    static char[] sharpsMap = new char[]{'S', 'S'};
    
    static char[] toUpperCaseCharArray(int ch) {
        char[] upperMap = {(char)ch};
        if (ch == 223) {
            upperMap = sharpsMap;
        }
        return upperMap;
    }
    static final int[] A = new int[256];
    static final String A_DATA = "\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u5800\u400f\u5000\u400f\u5800\u400f\u6000\u400f\u5000\u400f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u5000\u400f\u5000\u400f\u5000\u400f\u5800\u400f\u6000\u400c\u6800\030\u6800\030\u2800\030\u2800\u601a\u2800\030\u6800\030\u6800\030\ue800\025\ue800\026\u6800\030\u2800\031\u3800\030\u2800\024\u3800\030\u2000\030\u1800\u3609\u1800\u3609\u1800\u3609\u1800\u3609\u1800\u3609\u1800\u3609\u1800\u3609\u1800\u3609\u1800\u3609\u1800\u3609\u3800\030\u6800\030\ue800\031\u6800\031\ue800\031\u6800\030\u6800\030\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\ue800\025\u6800\030\ue800\026\u6800\033\u6800\u5017\u6800\033\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\ue800\025\u6800\031\ue800\026\u6800\031\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u5000\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u4800\u100f\u3800\f\u6800\030\u2800\u601a\u2800\u601a\u2800\u601a\u2800\u601a\u6800\034\u6800\034\u6800\033\u6800\034\000\u7002\ue800\035\u6800\031\u6800\u1010\u6800\034\u6800\033\u2800\034\u2800\031\u1800\u060b\u1800\u060b\u6800\033\u07fd\u7002\u6800\034\u6800\030\u6800\033\u1800\u050b\000\u7002\ue800\036\u6800\u080b\u6800\u080b\u6800\u080b\u6800\030\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\u6800\031\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\202\u7001\u07fd\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\u6800\031\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\201\u7002\u061d\u7002";
    static {
        {
            char[] data = A_DATA.toCharArray();
            if (!$assertionsDisabled && !(data.length == (256 * 2))) throw new AssertionError();
            int i = 0;
            int j = 0;
            while (i < (256 * 2)) {
                int entry = data[i++] << 16;
                A[j++] = entry | data[i++];
            }
        }
    }
}
