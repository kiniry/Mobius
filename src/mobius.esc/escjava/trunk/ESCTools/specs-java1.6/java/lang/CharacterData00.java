package java.lang;

class CharacterData00 {
    /*synthetic*/ static final boolean $assertionsDisabled = !CharacterData00.class.desiredAssertionStatus();
    
    CharacterData00() {
        
    }
    
    static int getProperties(int ch) {
        char offset = (char)ch;
        int props = A[Y[X[offset >> 5] | ((offset >> 1) & 15)] | (offset & 1)];
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
        int type = getType(ch);
        return (type == Character.TITLECASE_LETTER);
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
        if ((val & 131072) != 0) {
            if ((val & 133955584) == 133955584) {
                switch (ch) {
                case 304: 
                    mapChar = 105;
                    break;
                
                case 8486: 
                    mapChar = 969;
                    break;
                
                case 8490: 
                    mapChar = 107;
                    break;
                
                case 8491: 
                    mapChar = 229;
                    break;
                
                case 8072: 
                    mapChar = 8064;
                    break;
                
                case 8073: 
                    mapChar = 8065;
                    break;
                
                case 8074: 
                    mapChar = 8066;
                    break;
                
                case 8075: 
                    mapChar = 8067;
                    break;
                
                case 8076: 
                    mapChar = 8068;
                    break;
                
                case 8077: 
                    mapChar = 8069;
                    break;
                
                case 8078: 
                    mapChar = 8070;
                    break;
                
                case 8079: 
                    mapChar = 8071;
                    break;
                
                case 8088: 
                    mapChar = 8080;
                    break;
                
                case 8089: 
                    mapChar = 8081;
                    break;
                
                case 8090: 
                    mapChar = 8082;
                    break;
                
                case 8091: 
                    mapChar = 8083;
                    break;
                
                case 8092: 
                    mapChar = 8084;
                    break;
                
                case 8093: 
                    mapChar = 8085;
                    break;
                
                case 8094: 
                    mapChar = 8086;
                    break;
                
                case 8095: 
                    mapChar = 8087;
                    break;
                
                case 8104: 
                    mapChar = 8096;
                    break;
                
                case 8105: 
                    mapChar = 8097;
                    break;
                
                case 8106: 
                    mapChar = 8098;
                    break;
                
                case 8107: 
                    mapChar = 8099;
                    break;
                
                case 8108: 
                    mapChar = 8100;
                    break;
                
                case 8109: 
                    mapChar = 8101;
                    break;
                
                case 8110: 
                    mapChar = 8102;
                    break;
                
                case 8111: 
                    mapChar = 8103;
                    break;
                
                case 8124: 
                    mapChar = 8115;
                    break;
                
                case 8140: 
                    mapChar = 8131;
                    break;
                
                case 8188: 
                    mapChar = 8179;
                    break;
                
                }
            } else {
                int offset = val << 5 >> (5 + 18);
                mapChar = ch + offset;
            }
        }
        return mapChar;
    }
    
    static int toUpperCase(int ch) {
        int mapChar = ch;
        int val = getProperties(ch);
        if ((val & 65536) != 0) {
            if ((val & 133955584) == 133955584) {
                switch (ch) {
                case 181: 
                    mapChar = 924;
                    break;
                
                case 383: 
                    mapChar = 83;
                    break;
                
                case 8126: 
                    mapChar = 921;
                    break;
                
                case 8064: 
                    mapChar = 8072;
                    break;
                
                case 8065: 
                    mapChar = 8073;
                    break;
                
                case 8066: 
                    mapChar = 8074;
                    break;
                
                case 8067: 
                    mapChar = 8075;
                    break;
                
                case 8068: 
                    mapChar = 8076;
                    break;
                
                case 8069: 
                    mapChar = 8077;
                    break;
                
                case 8070: 
                    mapChar = 8078;
                    break;
                
                case 8071: 
                    mapChar = 8079;
                    break;
                
                case 8080: 
                    mapChar = 8088;
                    break;
                
                case 8081: 
                    mapChar = 8089;
                    break;
                
                case 8082: 
                    mapChar = 8090;
                    break;
                
                case 8083: 
                    mapChar = 8091;
                    break;
                
                case 8084: 
                    mapChar = 8092;
                    break;
                
                case 8085: 
                    mapChar = 8093;
                    break;
                
                case 8086: 
                    mapChar = 8094;
                    break;
                
                case 8087: 
                    mapChar = 8095;
                    break;
                
                case 8096: 
                    mapChar = 8104;
                    break;
                
                case 8097: 
                    mapChar = 8105;
                    break;
                
                case 8098: 
                    mapChar = 8106;
                    break;
                
                case 8099: 
                    mapChar = 8107;
                    break;
                
                case 8100: 
                    mapChar = 8108;
                    break;
                
                case 8101: 
                    mapChar = 8109;
                    break;
                
                case 8102: 
                    mapChar = 8110;
                    break;
                
                case 8103: 
                    mapChar = 8111;
                    break;
                
                case 8115: 
                    mapChar = 8124;
                    break;
                
                case 8131: 
                    mapChar = 8140;
                    break;
                
                case 8179: 
                    mapChar = 8188;
                    break;
                
                }
            } else {
                int offset = val << 5 >> (5 + 18);
                mapChar = ch - offset;
            }
        }
        return mapChar;
    }
    
    static int toTitleCase(int ch) {
        int mapChar = ch;
        int val = getProperties(ch);
        if ((val & 32768) != 0) {
            if ((val & 65536) == 0) {
                mapChar = ch + 1;
            } else if ((val & 131072) == 0) {
                mapChar = ch - 1;
            }
        } else if ((val & 65536) != 0) {
            mapChar = toUpperCase(ch);
        }
        return mapChar;
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
            switch (ch) {
            case 3057: 
                retval = 100;
                break;
            
            case 3058: 
                retval = 1000;
                break;
            
            case 4981: 
                retval = 40;
                break;
            
            case 4982: 
                retval = 50;
                break;
            
            case 4983: 
                retval = 60;
                break;
            
            case 4984: 
                retval = 70;
                break;
            
            case 4985: 
                retval = 80;
                break;
            
            case 4986: 
                retval = 90;
                break;
            
            case 4987: 
                retval = 100;
                break;
            
            case 4988: 
                retval = 10000;
                break;
            
            case 8543: 
                retval = 1;
                break;
            
            case 8556: 
                retval = 50;
                break;
            
            case 8557: 
                retval = 100;
                break;
            
            case 8558: 
                retval = 500;
                break;
            
            case 8559: 
                retval = 1000;
                break;
            
            case 8572: 
                retval = 50;
                break;
            
            case 8573: 
                retval = 100;
                break;
            
            case 8574: 
                retval = 500;
                break;
            
            case 8575: 
                retval = 1000;
                break;
            
            case 8576: 
                retval = 1000;
                break;
            
            case 8577: 
                retval = 5000;
                break;
            
            case 8578: 
                retval = 10000;
                break;
            
            case 12892: 
                retval = 32;
                break;
            
            case 12893: 
                retval = 33;
                break;
            
            case 12894: 
                retval = 34;
                break;
            
            case 12895: 
                retval = 35;
                break;
            
            case 12977: 
                retval = 36;
                break;
            
            case 12978: 
                retval = 37;
                break;
            
            case 12979: 
                retval = 38;
                break;
            
            case 12980: 
                retval = 39;
                break;
            
            case 12981: 
                retval = 40;
                break;
            
            case 12982: 
                retval = 41;
                break;
            
            case 12983: 
                retval = 42;
                break;
            
            case 12984: 
                retval = 43;
                break;
            
            case 12985: 
                retval = 44;
                break;
            
            case 12986: 
                retval = 45;
                break;
            
            case 12987: 
                retval = 46;
                break;
            
            case 12988: 
                retval = 47;
                break;
            
            case 12989: 
                retval = 48;
                break;
            
            case 12990: 
                retval = 49;
                break;
            
            case 12991: 
                retval = 50;
                break;
            
            default: 
                retval = -2;
                break;
            
            }
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
            switch (ch) {
            case 8234: 
                directionality = Character.DIRECTIONALITY_LEFT_TO_RIGHT_EMBEDDING;
                break;
            
            case 8235: 
                directionality = Character.DIRECTIONALITY_RIGHT_TO_LEFT_EMBEDDING;
                break;
            
            case 8236: 
                directionality = Character.DIRECTIONALITY_POP_DIRECTIONAL_FORMAT;
                break;
            
            case 8237: 
                directionality = Character.DIRECTIONALITY_LEFT_TO_RIGHT_OVERRIDE;
                break;
            
            case 8238: 
                directionality = Character.DIRECTIONALITY_RIGHT_TO_LEFT_OVERRIDE;
                break;
            
            default: 
                directionality = Character.DIRECTIONALITY_UNDEFINED;
                break;
            
            }
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
                
                case 383: 
                    mapChar = 83;
                    break;
                
                case 8126: 
                    mapChar = 921;
                    break;
                
                default: 
                    mapChar = Character.ERROR;
                    break;
                
                }
            }
        }
        return mapChar;
    }
    
    static char[] toUpperCaseCharArray(int ch) {
        char[] upperMap = {(char)ch};
        int location = findInCharMap(ch);
        if (location != -1) {
            upperMap = charMap[location][1];
        }
        return upperMap;
    }
    
    static int findInCharMap(int ch) {
        if (charMap == null || charMap.length == 0) {
            return -1;
        }
        int top;
        int bottom;
        int current;
        bottom = 0;
        top = charMap.length;
        current = top / 2;
        while (top - bottom > 1) {
            if (ch >= charMap[current][0][0]) {
                bottom = current;
            } else {
                top = current;
            }
            current = (top + bottom) / 2;
        }
        if (ch == charMap[current][0][0]) return current; else return -1;
    }
    static final char[][][] charMap;
    static final char[] X = ("\000\020 0@P`p\200\220\240\260\300\320\340\360\200\u0100\u0110\u0120\u0130\u0140\u0150\u0160\u0170\u0170\u0180\u0190\u01a0\u01b0\u01c0\u01d0\u01e0\u01f0\u0200\200\u0210\200\u0220\u0230\u0240\u0250\u0260\u0270\u0280\u0290\u02a0\u02b0\u02c0\u02d0\u02e0\u02f0\u0300\u0300\u0310\u0320\u0330\u0340\u0350\u0360\u0300\u0370\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0380\u0390\u03a0\u03b0\u03c0\u03d0\u03e0\u03f0\u0400\u0410\u0420\u0430\u0440\u0450\u0460\u0470\u03c0\u0480\u0490\u04a0\u04b0\u04c0\u04d0\u04e0\u04f0\u0500\u0510\u0520\u0530\u0540\u0550\u0520\u0530\u0560\u0570\u0520\u0580\u0590\u05a0\u05b0\u05c0\u05d0\u05e0\u0360\u05f0\u0600\u0610\u0360\u0620\u0630\u0640\u0650\u0660\u0670\u0680\u0360\u0690\u06a0\u06b0\u0360\u0360\u06c0\u06d0\u06e0\u0690\u0690\u06f0\u0690\u0690\u0700\u0690\u0710\u0720\u0690\u0730\u0690\u0740\u0750\u0760\u0770\u0750\u0690\u0780\u0790\u0360\u0690\u0690\u07a0\u05c0\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u07b0\u07c0\u0690\u0690\u07d0\u07e0\u07f0\u0800\u0810\u0690\u0820\u0830\u0840\u0850\u0690\u0860\u0870\u0690\u0880\u0360\u0360\u0890\u08a0\u08b0\u08c0\u0360\u0360\u0360\u08d0\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u08e0\u08f0\u0900\u0910\u0360\u0360\u0360\u0360\200\200\200\200\u0920\200\200\u0930\u0940\u0950\u0960\u0970\u0980\u0990\u09a0\u09b0\u09c0\u09d0\u09e0\u09f0\u0a00\u0a10\u0a20\u0a30\u0a40\u0a50\u0a60\u0a70\u0a80\u0a90\u0aa0\u0ab0\u0ac0\u0ad0\u0ae0\u0af0\u0b00\u0b10\u0b20\u0b30\u0b40\u0b50\u0b60\u0b70\u0b80\u0b90\u0ba0\u0360\u08d0\u0bb0\u0bc0\u0bd0\u0be0\u0bf0\u0c00\u0c10\u08d0\u08d0\u08d0\u08d0\u08d0\u0c20\u0c30\u0c40\u0c50\u08d0\u08d0\u0c60\u0c70\u0c80\u0360\u0360\u0c90\u0ca0\u0cb0\u0cc0\u0cd0\u0ce0\u0cf0\u0d00\u08d0\u08d0\u08d0\u08d0\u08d0\u08d0\u08d0\u08d0\u0d10\u0d10\u0d10\u0d10\u0d20\u0d30\u0d40\u0d50\u0d60\u0d70\u0d80\u0d90\u0da0\u0db0\u0dc0\u0dd0\u0de0\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0df0\u08d0\u08d0\u0e00\u08d0\u08d0\u08d0\u08d0\u08d0\u08d0\u0e10\u0e20\u0e30\u0e40\u05c0\u0690\u0e50\u0e60\u0690\u0e70\u0e80\u0e90\u0690\u0690\u0ea0\u0870\u0360\u0eb0\u0ec0\u0ed0\u0ee0\u0ef0\u0ed0\u0f00\u0f10\u0f20\u0b60\u0b60\u0b60\u0f30\u0b60\u0b60\u0f40\u0f50\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0f60\u08d0\u08d0\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0f70\u0360\u0360\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0f80\u08d0\u0bb0\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0360\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0f90\u0360\u0360\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fa0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0fb0\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0690\u0fc0\u0690\u0fd0\u0360\u0360\u0360\u0360\u0fe0\u0ff0\u1000\u0300\u0300\u1010\u1020\u0300\u0300\u0300\u0300\u0300\u0300\u0300\u0300\u0300\u0300\u1030\u1040\u0300\u1050\u0300\u1060\u1070\u1080\u1090\u10a0\u10b0\u0300\u0300\u0300\u10c0\u10d0 \u10e0\u10f0\u1100\u1110\u1120\u1130").toCharArray();
    static final char[] Y = ("\000\000\000\000\002\004\006\000\000\000\000\000\000\000\b\004\n\f\016\020\022\024\026\030\032\032\032\032\032\034\036 \"$$$$$$$$$$$$&(*,............024\000\0006\000\000\000\000\000\000\000\000\000\000\000\000\0008::<>@BDFHJLNPRTVVVVVVVVVVVXVVVZ\\\\\\\\\\\\\\\\\\\\\\^\\\\\\`bbbbbbbbbbbbbbbbbbbbbbbbdbbbfhhhhhhhjbbbbbbbbbbbbbbbbbbbbbbblhhjnbbprtvxzr|~b\200\202\204bbb\206\210\200b\206\212\214h\216b\220b\222\224\224\226\230\232\226\234hhhhhhh\236bbbbbbbbb\240\232b\242bbbb\244bbbbbbbbb\200\246\250\250\250\250\250\250\250\250\250\250\250\250\200\252\254\256\260\262\200\200\264\266\200\200\270\200\200\272\200\274\276\200\200\200\200\200\300\302\200\200\300\304\200\200\200\306\200\200\200\200\200\200\200\200\200\200\200\200\200\200\310\310\310\310\312\314\310\310\310\316\316\320\320\320\320\320\310\316\316\316\316\316\316\316\310\310\322\316\316\316\316\322\316\316\316\316\316\316\316\316\324\324\324\324\324\324\324\324\324\324\324\324\324\324\324\324\324\324\326\324\324\324\324\324\324\324\324\324\250\250\330\324\324\324\324\324\324\324\324\324\250\250\316\250\250\332\250\334\250\250\316\336\340\342\344\346\350VVVVVVVV\352VVVV\354\356\360\\\\\\\\\\\\\\\\\362\\\\\\\\\364\366\370\372\374\376bbbbbbbbbbbb\u0100\u0102\u0104\u0106\u0108b\250\250\u010a\u010a\u010a\u010a\u010a\u010a\u010a\u010aVVVVVVVVVVVVVVVV\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\u010c\u010c\u010c\u010c\u010c\u010c\u010c\u010cb\u010e\324\u0110\u0112bbbbbbbbbbb\u0114hhhhhh\u0116bbbbbbbbbbbbbbbbbbb\250b\250\250\250bbbbbbbb\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\u0118\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011a\u011c\u011e\u0120\u0120\u0120\u0122\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0124\u0126\u0128\u012a\250\250\330\324\324\324\324\324\324\324\324\330\324\324\324\324\324\324\324\324\324\324\324\330\324\u012c\u012c\u012e\u0110\250\250\250\250\250\u0130\u0130\u0130\u0130\u0130\u0130\u0130\u0130\u0130\u0130\u0130\u0130\u0130\u0132\250\250\u0130\u0134\u0136\250\250\250\250\250\u0138\u0138\250\250\250\250\u013a<\324\324\324\250\250\u013c\250\u013c\u013e\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0142\250\250\u0144\u0140\u0140\u0140\u0140\u0146\324\324\324\324\324\324\u0110\250\250\250\u0148\u0148\u0148\u0148\u0148\u014a\u014c\u0140\u014e\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0150\324\324\324\u0152\u0154\324\324\u0156\u0158\u015a\324\324\u0140\032\032\032\032\032\u0140\u015c\u015e\u0160\u0160\u0160\u0160\u0160\u0160\u0160\u0162\u0146\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\324\324\324\324\324\324\324\324\324\324\324\324\324\u0110\u013e\u0140\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\u0140\u0140\u0140\324\324\324\324\324\u014e\250\250\250\250\250\250\250\330\u0164\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\250\u0166\u0168\u016a\324\324\324\u0164\u0168\u016a\250\u016c\324\u0110\250\224\224\224\224\224\324\u0120\u016e\u016e\u016e\u016e\u016e\u0170\250\250\250\250\250\250\250\330\u0168\u0172\224\224\224\u0174\u0172\u0174\u0172\224\224\224\224\224\224\224\224\224\224\u0174\224\224\224\u0174\u0174\250\224\224\250\u0166\u0168\u016a\324\u0110\u0176\u0178\u0176\u016a\250\250\250\250\u0176\250\250\224\u0172\224\324\250\u016e\u016e\u016e\u016e\u016e\224:\u017a\u017a\u017c\u017e\250\250\330\u0164\u0172\224\224\u0174\250\u0172\u0174\u0172\224\224\224\224\224\224\224\224\224\224\u0174\224\224\224\u0174\224\u0172\u0174\224\250\u0110\u0168\u016a\u0110\250\330\u0110\330\324\250\250\250\250\250\u0172\224\u0174\u0174\250\250\250\u016e\u016e\u016e\u016e\u016e\324\224\u0174\250\250\250\250\250\330\u0164\u0172\224\224\224\224\u0172\224\u0172\224\224\224\224\224\224\224\224\224\224\u0174\224\224\224\u0174\224\u0172\224\224\250\u0166\u0168\u016a\324\324\330\u0164\u0176\u016a\250\u0174\250\250\250\250\250\250\250\224\324\250\u016e\u016e\u016e\u016e\u016e\u0180\250\250\250\250\250\250\250\224\224\224\224\u0174\224\224\224\u0174\224\u0172\224\224\250\u0166\u016a\u016a\324\250\u0176\u0178\u0176\u016a\250\250\250\250\u0164\250\250\224\u0172\224\250\250\u016e\u016e\u016e\u016e\u016e\u0182\250\250\250\250\250\250\250\250\u0166\u0172\224\224\u0174\250\224\u0174\224\224\250\u0172\u0174\u0174\224\250\u0172\u0174\250\224\u0174\250\224\224\224\224\u0172\224\250\250\u0168\u0164\u0178\250\u0168\u0178\u0168\u016a\250\250\250\250\u0176\250\250\250\250\250\250\250\u0184\u016e\u016e\u016e\u016e\u0186\u0188<<\u018a\u018c\250\250\u0176\u0168\u0172\224\224\224\u0174\224\u0174\224\224\224\224\224\224\224\224\224\224\224\u0174\224\224\224\224\224\u0172\224\224\250\250\324\u0164\u0168\u0178\324\u0110\324\324\250\250\250\330\u0110\250\250\250\250\224\250\250\u016e\u016e\u016e\u016e\u016e\250\250\250\250\250\250\250\250\250\u0168\u0172\224\224\224\u0174\224\u0174\224\224\224\224\224\224\224\224\224\224\224\u0174\224\224\224\224\224\u0172\224\224\250\u0166\u018e\u0168\u0168\u0178\u0190\u0178\u0168\324\250\250\250\u0176\u0178\250\250\250\u0174\224\224\224\224\u0174\224\224\224\224\224\224\224\224\250\250\u0168\u016a\324\250\u0168\u0178\u0168\u016a\250\250\250\250\u0176\250\250\250\250\250\u0168\u0172\224\224\224\224\224\224\224\224\u0174\250\224\224\224\224\224\224\224\224\224\224\224\224\u0172\224\224\224\224\u0172\250\224\224\224\u0174\250\u0110\250\u0176\u0168\324\u0110\u0110\u0168\u0168\u0168\u0168\250\250\250\250\250\250\250\250\250\u0168\u0170\250\250\250\250\250\u0172\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u016c\224\324\324\324\u0110\250\u0180\224\224\224\u0192\324\324\324\u0194\u0196\u0196\u0196\u0196\u0196\u0120\250\250\u0172\u0174\u0174\u0172\u0174\u0174\u0172\250\250\250\224\224\u0172\224\224\224\u0172\224\u0172\u0172\250\224\u0172\224\u016c\224\324\324\324\330\u0166\250\224\224\u0174\332\324\324\324\250\u0196\u0196\u0196\u0196\u0196\250\224\250\u0198\u019a\u0120\u0120\u0120\u0120\u0120\u0120\u0120\u019c\u019a\u019a\324\u019a\u019a\u019a\u019e\u019e\u019e\u019e\u019e\u01a0\u01a0\u01a0\u01a0\u01a0\u010e\u010e\u010e\u01a2\u01a2\u0168\224\224\224\224\u0172\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\250\250\330\324\324\324\324\324\324\u0164\324\324\u0194\324\224\224\250\250\324\324\324\324\330\324\324\324\324\324\324\324\324\324\324\324\324\324\324\324\324\324\u0110\u019a\u019a\u019a\u019a\u01a4\u019a\u019a\u017e\u01a6\250\250\250\250\250\250\250\250\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0172\224\224\u0172\u0174\u016a\324\u0164\u0110\250\324\u016a\250\250\250\u019e\u019e\u019e\u019e\u019e\u0120\u0120\u0120\224\224\224\u0168\324\250\250\250\372\372\372\372\372\372\372\372\372\372\372\372\372\372\372\372\372\372\372\250\250\250\250\250\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\u0128\250\250\224\224\224\224\224\224\224\224\224\224\224\224\224\250\250\u0172\224\u0174\250\250\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\250\250\250\224\224\224\u0174\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\u0174\224\224\250\224\224\224\u0174\u0174\224\224\250\224\224\224\u0174\u0174\224\224\250\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\u0174\224\224\250\224\224\224\u0174\u0174\224\224\250\224\224\224\u0174\224\224\224\u0174\224\224\224\224\224\224\224\224\224\224\224\u0174\224\224\224\224\224\224\224\224\224\224\224\u0174\224\224\224\224\224\224\224\224\224\u0174\250\250\u0128\u0120\u0120\u0120\u01a8\u01aa\u01aa\u01aa\u01aa\u01ac\u01ae\u01a0\u01a0\u01a0\u01b0\250\224\224\224\224\224\224\224\224\224\224\u0174\250\250\250\250\250\224\224\224\224\224\224\u01b2\u01b4\224\224\224\u0174\250\250\250\250\u01b6\224\224\224\224\224\224\224\224\224\224\224\224\u01b8\u01ba\250\224\224\224\224\224\u01b2\u0120\u01bc\u01be\250\250\250\250\250\250\250\224\224\224\224\224\224\u0174\224\224\324\u0110\250\250\250\250\250\224\224\224\224\224\224\224\224\224\324\u0194\u0170\250\250\250\250\224\224\224\224\224\224\224\224\224\324\250\250\250\250\250\250\224\224\224\224\224\224\u0174\224\u0174\324\250\250\250\250\250\250\224\224\224\224\224\224\224\224\224\224\u01c0\u016a\324\324\324\u0168\u0168\u0168\u0168\u0164\u016a\324\324\324\324\324\u0120\u01c2\u0120\u01c4\u016c\250\u019e\u019e\u019e\u019e\u019e\250\250\250\u01c6\u01c6\u01c6\u01c6\u01c6\250\250\250\020\020\020\u01c8\020\u01ca\324\u01cc\u0196\u0196\u0196\u0196\u0196\250\250\250\224\u01ce\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\250\250\250\250\224\224\224\224\u016c\250\250\250\250\250\250\250\250\250\250\250\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\250\324\u0164\u0168\u016a\u01d0\u01d2\250\250\u0168\u0164\u0168\u0168\u016a\324\250\250\u018c\250\020\u016e\u016e\u016e\u016e\u016e\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\250\224\224\u0174\250\250\250\250\250<<<<<<<<<<<<<<<<\200\200\200\200\200\200\200\200\200\200\200\200\200\200\200\200\200\200\200\200\200\200\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\310\200\200\200\200\200\250\250\250\250\250\250\250\250\250\250bbbbbbbbbbb\u01d4\u01d4\u01d6\250\250bbbbbbbbbbbbb\250\250\250\u01d8\u01d8\u01d8\u01d8\u01da\u01da\u01da\u01da\u01d8\u01d8\u01d8\250\u01da\u01da\u01da\250\u01d8\u01d8\u01d8\u01d8\u01da\u01da\u01da\u01da\u01d8\u01d8\u01d8\u01d8\u01da\u01da\u01da\u01da\u01d8\u01d8\u01d8\250\u01da\u01da\u01da\250\u01dc\u01dc\u01dc\u01dc\u01de\u01de\u01de\u01de\u01d8\u01d8\u01d8\u01d8\u01da\u01da\u01da\u01da\u01e0\u01e2\u01e2\u01e4\u01e6\u01e8\u01ea\250\u01d4\u01d4\u01d4\u01d4\u01ec\u01ec\u01ec\u01ec\u01d4\u01d4\u01d4\u01d4\u01ec\u01ec\u01ec\u01ec\u01d4\u01d4\u01d4\u01d4\u01ec\u01ec\u01ec\u01ec\u01d8\u01d4\u01ee\u01d4\u01da\u01f0\u01f2\u01f4\316\u01d4\u01ee\u01d4\u01f6\u01f6\u01f2\316\u01d8\u01d4\250\u01d4\u01da\u01f8\u01fa\316\u01d8\u01d4\u01fc\u01d4\u01da\u01fe\u0200\316\250\u01d4\u01ee\u01d4\u0202\u0204\u01f2\u0206\u0208\u0208\u0208\u020a\u0208\u020c\u020e\u0210\u0212\u0212\u0212\020\u0214\u0216\u0214\u0216\020\020\020\020\u0218\u021a\u021a\u021c\u021e\u021e\u0220\020\u0222\u0224\020\u0226\u0228\020\u022a\u022c\020\020\020\020\020\u022e\u0230\u0232\250\250\250\u0234\u020e\u020e\250\250\250\u020e\u020e\u020e\u0236\250HHH\u0238\u022a\u023a\u023c\u023c\u023c\u023c\u023c\u0238\u022a\u023e\250\250\250\250\250\250\250\250:::::::::\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\324\324\324\324\324\324\u0240\u0112\u0154\u0112\u0154\324\324\u0110\250\250\250\250\250\250\250\250\250\250<\u0242<\u0244<\u0246\372\200\372\u0248\u0244<\u0244\372\372<<<\u0242\u024a\u0242\u024c\372\u024e\372\u0244\220\224\u0250<\u0252\372\036\u0254\u0256\200\200\u0258\250\250\250\u025aRRRRRR\u025c\u025c\u025c\u025c\u025c\u025c\u025e\u025e\u0260\u0260\u0260\u0260\u0260\u0260\u0262\u0262\u0264\u0266\250\250\250\250\250\250\u0254\u0254\u0268<<\u0254<<\u0268\u0258<\u0268<<<\u0268<<<<<<<<<<<<<<<\u0254<\u0268\u0268<<<<<<<<<<<<<<<\u0254\u0254\u0254\u0254\u0254\u0254\u026a\u026c\036\u0254\u026c\u026c\u026c\u0254\u026a\u0238\u026a\036\u0254\u026c\u026c\u026a\u026c\036\036\036\u0254\u026a\u026c\u026c\u026c\u026c\u0254\u0254\u026a\u026a\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\036\u0254\u0254\u026c\u026c\u0254\u0254\u0254\u0254\u026a\036\036\u026c\u026c\u026c\u026c\u0254\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\036\u026a\u026c\036\u0254\u0254\036\u0254\u0254\u0254\u0254\u026c\u0254\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\036\u0254\u0254\u026c\u0254\u0254\u0254\u0254\u026a\u026c\u026c\u0254\u026c\u0254\u0254\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u0254\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c<<<<\u026c\u026c<<<<<<<<<<\u026c<<<\u026e\u0270<<<<<\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u0272\u0268<<<<<<<<<<<\u0274<<\u0258\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u01a2\u0276<<<<<<<<<<<<\u018c\250\250\250\250\250\250\250<<<\u018c\250\250\250\250\250\250\250\250\250\250\250\250<<<<<\u018c\250\250\250\250\250\250\250\250\250\250\u0278\u0278\u0278\u0278\u0278\u0278\u0278\u0278\u0278\u0278\u027a\u027a\u027a\u027a\u027a\u027a\u027a\u027a\u027a\u027a\u027c\u027c\u027c\u027c\u027c\u027c\u027c\u027c\u027c\u027c\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u027e\u027e\u027e\u027e\u027e\u027e\u027e\u027e\u027e\u027e\u027e\u027e\u027e\u0280\u0280\u0280\u0280\u0280\u0280\u0280\u0280\u0280\u0280\u0280\u0280\u0280\u0282\u0284\u0284\u0284\u0284\u0286\u0288\u0288\u0288\u0288\u028a<<<<<<<<<<<\u0258<<<<\u0258<<<<<<<<<<<<<<<<<<<<<<<<<<<\u0254\u0254\u0254\u0254<<<<<<<<<<<<\u028c<<<<<<<<<<\u0258<<<<<<<\250<<<<<<<<<\250\250\250\250\250\250\250<\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\u028c<\u018c<<\250<<<<<<<<<<<<<<\u028c<<<<<<<<<<<<<<<<<\u028c\u028c<\u018c\250\u018c<<<\u018c\u028c<<<\022\022\022\022\022\022\022\u028e\u028e\u028e\u028e\u028e\u0290\u0290\u0290\u0290\u0290\u0292\u0292\u0292\u0292\u0292\u018c\250<<<<<<<<<<<<\u028c<<<<<<\u018c\250\250\250\250\250\250\250\250\u0254\u026a\u026c\036\u0254\u0254\u026c\036\u0254\u026c\u026c\022\022\022\250\250\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u022a\u0294\u0294\u0294\u0294\u0294\u0294\u0294\u0294\u0294\u0294\u0296\u026a\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u0254\u0254\u0254\u0254\036\u0254\u0254\u0254\u026c\u026c\u026c\u0254\u026a\u0254\u0254\u026c\u026c\036\u026c\u0254\022\022\036\u0254\u026a\u026a\u026c\u0254\u026c\u0254\u0254\u0254\u0254\u0254\u026c\u026c\u026c\u0254\022\u0254\u0254\u0254\u0254\u0254\u0254\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\036\u026c\u026c\u0254\036\036\u026a\u026a\u026c\036\u0254\u0254\u026c\u0254\u0254\u0254\u026c\036\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u0254\u026a\036\u0254\u0254\u0254\u0254\u0254\u026c\u0254\u0254\u026c\u026c\u026a\036\u026a\036\u0254\u026a\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u0254\u026c\u026c\u026c\u026c\u026a\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\u026c\036\u0254\u0254\036\036\u0254\u026c\u026c\036\u0254\u0254\u026c\036\u0254\u026a\u0254\u026a\u026c\u026c\u026a\u0254<<<<<<<\250\250\250\250\250\250\250\250\250<<<<<<<<<<<<<\u028c<<<<<<<<<<<<\250\250\250\250\250\250<<<<<<<<<<<\250\250\250\250\250\250\250\250\250\250\250\250\250<<<<<<\250\250\n\020\u0298\u029a\022\022\022\022\022<\022\022\022\022\u029c\u029e\u02a0\u02a2\u02a2\u02a2\u02a2\324\324\324\u02a4\310\310<\u02a6\u02a8\u02aa<\224\224\224\224\224\224\224\224\224\224\224\u0174\330\u02ac\u02ae\u02b0\u02b2\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u02b4\310\u02b0\250\250\u0172\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\250\u0172\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\u019a\u02b6\u02b6\u019a\u019a\u019a\u019a\u019a\250\250\250\250\250\250\250\250\224\224\224\224\224\224\224\224\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u0272\u018c\u02b8\u02b8\u02b8\u02b8\u02b8\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\250\250\250\250\250\250\u02ba\u02bc\u02bc\u02bc\u02bc\u02bcRR\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a<\u01a6\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u02beRRRRRRR\u019a\u019a\u019a\u019a\u019a\u019a<<\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u017e\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u0272<\u0274\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a<\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u019a\u0272\224\224\224\224\224\224\224\224\224\224\224\250\250\250\250\250\224\224\224\250\250\250\250\250\250\250\250\250\250\250\250\250\224\224\224\224\224\224\u0174\250<<<<<<<<\224\224\250\250\250\250\250\250\250\250\250\250\250\250\250\250\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c0\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\u02c2\224\224\224\224\224\224\224\250\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\250\250\250\250\250\250\250\250\250\250\u01d4\u01d4\u01d4\u01ee\250\250\250\250\250\u02c4\u01d4\u01d4\250\250\u02c6\u02c8\u0130\u0130\u0130\u0130\u02ca\u0130\u0130\u0130\u0130\u0130\u0130\u0132\u0130\u0130\u0132\u0132\u0130\u02c6\u0132\u0130\u0130\u0130\u0130\u0130\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\u013e\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u01a2\250\250\250\250\250\250\250\250\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\250\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\250\u0140\u0140\u0140\u0140\u0140\u0140\u02cc\250\324\324\324\324\324\324\324\324\250\250\250\250\250\250\250\250\324\324\250\250\250\250\250\250\u02ce\u02d0\u02d2\u02d4\u02d4\u02d4\u02d4\u02d4\u02d4\u02d4\u02d6\u02d8\u02d6\020\u0226\u02da\034\u02dc\u02de\020\u029c\u02d4\u02d4\u02e0\020\u02e2\u0254\u02e4\u02e6\u0220\250\250\u0140\u0140\u0142\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0140\u0142\u0162\u0232\f\016\020\022\024\026\030\032\032\032\032\032\034\036 ,............02\u022a\u022c\022\u0226\224\224\224\224\224\u02b0\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\310\224\224\224\224\224\224\224\224\224\224\224\224\224\224\224\u0174\250\224\224\224\250\224\224\224\250\224\224\224\250\224\u0174\250:\u02e8\u018a\u02ea\u0258\u0254\u0268\u018c\250\250\250\250\u0162\u020e<\250").toCharArray();
    static final int[] A = new int[748];
    static final String A_DATA = "\u4800\u100f\u4800\u100f\u4800\u100f\u5800\u400f\u5000\u400f\u5800\u400f\u6000\u400f\u5000\u400f\u5000\u400f\u5000\u400f\u6000\u400c\u6800\030\u6800\030\u2800\030\u2800\u601a\u2800\030\u6800\030\u6800\030\ue800\025\ue800\026\u6800\030\u2800\031\u3800\030\u2800\024\u3800\030\u2000\030\u1800\u3609\u1800\u3609\u3800\030\u6800\030\ue800\031\u6800\031\ue800\031\u6800\030\u6800\030\202\u7fe1\202\u7fe1\202\u7fe1\202\u7fe1\ue800\025\u6800\030\ue800\026\u6800\033\u6800\u5017\u6800\033\201\u7fe2\201\u7fe2\201\u7fe2\201\u7fe2\ue800\025\u6800\031\ue800\026\u6800\031\u4800\u100f\u4800\u100f\u5000\u100f\u3800\f\u6800\030\u2800\u601a\u2800\u601a\u6800\034\u6800\034\u6800\033\u6800\034\000\u7002\ue800\035\u6800\031\u6800\u1010\u6800\034\u6800\033\u2800\034\u2800\031\u1800\u060b\u1800\u060b\u6800\033\u07fd\u7002\u6800\034\u6800\030\u6800\033\u1800\u050b\000\u7002\ue800\036\u6800\u080b\u6800\u080b\u6800\u080b\u6800\030\202\u7001\202\u7001\202\u7001\u6800\031\202\u7001\u07fd\u7002\201\u7002\201\u7002\201\u7002\u6800\031\201\u7002\u061d\u7002\006\u7001\005\u7002\u07ff\uf001\u03a1\u7002\000\u7002\006\u7001\005\u7002\006\u7001\005\u7002\u07fd\u7002\u061e\u7001\006\u7001\000\u7002\u034a\u7001\u033a\u7001\006\u7001\005\u7002\u0336\u7001\u0336\u7001\006\u7001\005\u7002\000\u7002\u013e\u7001\u032a\u7001\u032e\u7001\006\u7001\u033e\u7001\u067d\u7002\u034e\u7001\u0346\u7001\000\u7002\000\u7002\u034e\u7001\u0356\u7001\u05f9\u7002\u035a\u7001\u036a\u7001\006\u7001\005\u7002\u036a\u7001\005\u7002\u0366\u7001\u0366\u7001\006\u7001\005\u7002\u036e\u7001\000\u7002\000\u7005\000\u7002\u0721\u7002\000\u7005\000\u7005\n\uf001\007\uf003\t\uf002\n\uf001\007\uf003\t\uf002\t\uf002\006\u7001\005\u7002\u013d\u7002\u07fd\u7002\n\uf001\u067e\u7001\u0722\u7001\u05fa\u7001\000\u7002\000\u7002\u7800\000\u7800\000\u7800\000\000\u7002\u0349\u7002\u0339\u7002\000\u7002\u0335\u7002\u0335\u7002\000\u7002\u0329\u7002\000\u7002\u032d\u7002\u0335\u7002\000\u7002\000\u7002\u033d\u7002\u0345\u7002\u034d\u7002\000\u7002\u034d\u7002\u0355\u7002\000\u7002\000\u7002\u0359\u7002\u0369\u7002\000\u7002\000\u7002\u0369\u7002\u0365\u7002\u0365\u7002\u036d\u7002\000\u7002\000\u7004\000\u7004\000\u7004\u6800\u7004\u6800\u7004\000\u7004\u6800\033\u6800\033\u6800\u7004\u6800\u7004\000\u7004\u6800\033\u4000\u3006\u4000\u3006\u4000\u3006\u46b1\u3006\u7800\000\u4000\u3006\000\u7004\u7800\000\u6800\030\u7800\000\232\u7001\u6800\030\226\u7001\226\u7001\226\u7001\u7800\000\u0102\u7001\u7800\000\376\u7001\376\u7001\u07fd\u7002\202\u7001\u7800\000\202\u7001\231\u7002\225\u7002\225\u7002\225\u7002\u07fd\u7002\201\u7002}\u7002\201\u7002\u0101\u7002\375\u7002\375\u7002\u7800\000\371\u7002\345\u7002\000\u7001\000\u7001\000\u7001\275\u7002\331\u7002\000\u7002\u0159\u7002\u0141\u7002\u07e5\u7002\000\u7002\u0712\u7001\u0181\u7002\u6800\031\006\u7001\005\u7002\u07e6\u7001\u0142\u7001\u0142\u7001\u0141\u7002\u0141\u7002\000\034\u4000\u3006\u4000\u3006\u7800\000\u4000\007\u4000\007\000\u7001\006\u7001\005\u7002\u7800\000\u7800\000\302\u7001\302\u7001\302\u7001\302\u7001\u7800\000\u7800\000\000\u7004\000\030\000\030\u7800\000\301\u7002\301\u7002\301\u7002\301\u7002\u07fd\u7002\u7800\000\000\030\u6800\024\u7800\000\u0800\030\u4000\u3006\u4000\u3006\u0800\030\u0800\u7005\u0800\u7005\u0800\u7005\u7800\000\u0800\u7005\u0800\030\u0800\030\u7800\000\u1000\u1010\u1000\u1010\u3800\030\u1000\030\u7800\000\u1000\030\u7800\000\u1000\u7005\u1000\u7005\u1000\u7005\u1000\u7005\u7800\000\u1000\u7004\u1000\u7005\u1000\u7005\u4000\u3006\u3000\u3409\u3000\u3409\u2800\030\u3000\030\u3000\030\u1000\030\u4000\u3006\u1000\u7005\u1000\030\u1000\u7005\u4000\u3006\u1000\u1010\u4000\007\u4000\u3006\u4000\u3006\u1000\u7004\u1000\u7004\u4000\u3006\u4000\u3006\u6800\034\u1000\u7005\u1000\034\u1000\034\u1000\u7005\u1000\030\u1000\030\u7800\000\u4800\u1010\u4000\u3006\000\u3008\u4000\u3006\000\u7005\000\u3008\000\u3008\000\u3008\u4000\u3006\000\u7005\u4000\u3006\000\u3749\000\u3749\000\030\u7800\000\u7800\000\000\u7005\000\u7005\u7800\000\u7800\000\000\u3008\000\u3008\u7800\000\000\u05ab\000\u05ab\000\013\000\u06eb\000\034\u7800\000\u7800\000\u2800\u601a\000\034\000\u7005\u7800\000\000\u3749\000\u074b\000\u080b\000\u080b\u6800\034\u6800\034\u2800\u601a\u6800\034\u7800\000\000\u3008\000\u3006\000\u3006\000\u3008\000\u7004\u4000\u3006\u4000\u3006\000\030\000\u3609\000\u3609\000\u7005\000\034\000\034\000\034\000\030\000\034\000\u3409\000\u3409\000\u080b\000\u080b\u6800\025\u6800\026\u4000\u3006\000\034\u7800\000\000\034\000\030\000\u3709\000\u3709\000\u3709\000\u070b\000\u042b\000\u054b\000\u080b\000\u080b\u7800\000\000\u7005\000\030\000\030\000\u7005\u6000\u400c\000\u7005\000\u7005\u6800\025\u6800\026\u7800\000\000\u746a\000\u746a\000\u746a\u7800\000\000\u1010\000\u1010\000\030\000\u7004\000\030\u2800\u601a\u6800\u060b\u6800\u060b\u6800\024\u6800\030\u6800\030\u4000\u3006\u6000\u400c\u7800\000\000\u7005\000\u7004\u4000\u3006\u4000\u3008\u4000\u3008\u4000\u3008\u07fd\u7002\u07fd\u7002\u07fd\u7002\355\u7002\u07e1\u7002\u07e1\u7002\u07e2\u7001\u07e2\u7001\u07fd\u7002\u07e1\u7002\u7800\000\u07e2\u7001\u06d9\u7002\u06d9\u7002\u06a9\u7002\u06a9\u7002\u0671\u7002\u0671\u7002\u0601\u7002\u0601\u7002\u0641\u7002\u0641\u7002\u0609\u7002\u0609\u7002\u07ff\uf003\u07ff\uf003\u07fd\u7002\u7800\000\u06da\u7001\u06da\u7001\u07ff\uf003\u6800\033\u07fd\u7002\u6800\033\u06aa\u7001\u06aa\u7001\u0672\u7001\u0672\u7001\u7800\000\u6800\033\u07fd\u7002\u07e5\u7002\u0642\u7001\u0642\u7001\u07e6\u7001\u6800\033\u0602\u7001\u0602\u7001\u060a\u7001\u060a\u7001\u6800\033\u7800\000\u6000\u400c\u6000\u400c\u6000\u400c\u6000\f\u6000\u400c\u4800\u400c\u4800\u1010\u4800\u1010\000\u1010\u0800\u1010\u6800\024\u6800\024\u6800\035\u6800\036\u6800\025\u6800\035\u6000\u400d\u5000\u400e\u7800\u1010\u7800\u1010\u7800\u1010\u6000\f\u2800\030\u2800\030\u2800\030\u6800\030\u6800\030\ue800\035\ue800\036\u6800\030\u6800\030\u6800\u5017\u6800\u5017\u6800\030\u6800\031\ue800\025\ue800\026\u6800\030\u6800\031\u6800\030\u6800\u5017\u7800\000\u7800\000\u6800\030\u7800\000\u6000\u400c\u1800\u060b\000\u7002\u2800\031\u2800\031\ue800\026\000\u7002\u1800\u040b\u1800\u040b\ue800\026\u7800\000\u4000\u3006\u4000\007\000\u7001\u6800\034\u6800\034\000\u7001\000\u7002\000\u7001\000\u7001\000\u7002\u07fe\u7001\u6800\034\u07fe\u7001\u07fe\u7001\u2800\034\000\u7002\000\u7005\000\u7002\u7800\000\000\u7002\u6800\031\u6800\031\u6800\031\000\u7001\u6800\034\u6800\031\u7800\000\u6800\u080bB\u742aB\u742aB\u780aB\u780aA\u762aA\u762aA\u780aA\u780a\000\u780a\000\u780a\000\u780a\000\u700a\u6800\031\u6800\034\u6800\031\ue800\031\ue800\031\ue800\031\u6800\034\ue800\025\ue800\026\u6800\034\000\034\u6800\034\u6800\034\000\034\u6800\030\u6800\034\u1800\u042b\u1800\u042b\u1800\u05ab\u1800\u05ab\u1800\u072b\u1800\u072bj\034j\034i\034i\034\u1800\u06cb\u6800\u040b\u6800\u040b\u6800\u040b\u6800\u040b\u6800\u058b\u6800\u058b\u6800\u058b\u6800\u058b\u6800\u042b\u7800\000\u6800\034\u6800\u056b\u6800\u056b\u6800\u042b\u6800\u042b\u6800\u06eb\u6800\u06eb\ue800\026\ue800\025\ue800\026\u6800\031\u6800\034\000\u7004\000\u7005\000\u772a\u6800\024\u6800\025\u6800\026\u6800\026\u6800\034\000\u740a\000\u740a\000\u740a\u6800\024\000\u7004\000\u764a\000\u776a\000\u748a\000\u7004\000\u7005\u6800\030\u4000\u3006\u6800\033\u6800\033\000\u7004\000\u7004\000\u7005\u6800\024\000\u7005\000\u7005\u6800\u5017\000\u05eb\000\u05eb\000\u042b\000\u042b\u6800\034\u6800\u048b\u6800\u048b\u6800\u048b\000\034\u6800\u080b\000\023\000\023\000\022\000\022\u7800\000\u07fd\u7002\u7800\000\u0800\u7005\u4000\u3006\u0800\u7005\u0800\u7005\u2800\031\u1000\u601a\u6800\034\u6800\030\u6800\024\u6800\024\u6800\u5017\u6800\u5017\u6800\025\u6800\026\u6800\025\u6800\026\u6800\030\u6800\030\u6800\025\u6800\u5017\u6800\u5017\u3800\030\u7800\000\u6800\030\u3800\030\u6800\026\u2800\030\u2800\031\u2800\024\u6800\031\u7800\000\u6800\030\u2800\u601a\u6800\031\u6800\033\u2800\u601a\u7800\000";
    static {
        charMap = new char[][][]{{{'\337'}, {'S', 'S'}}, {{'\u0130'}, {'\u0130'}}, {{'\u0149'}, {'\u02bc', 'N'}}, {{'\u01f0'}, {'J', '\u030c'}}, {{'\u0390'}, {'\u0399', '\u0308', '\u0301'}}, {{'\u03b0'}, {'\u03a5', '\u0308', '\u0301'}}, {{'\u0587'}, {'\u0535', '\u0552'}}, {{'\u1e96'}, {'H', '\u0331'}}, {{'\u1e97'}, {'T', '\u0308'}}, {{'\u1e98'}, {'W', '\u030a'}}, {{'\u1e99'}, {'Y', '\u030a'}}, {{'\u1e9a'}, {'A', '\u02be'}}, {{'\u1f50'}, {'\u03a5', '\u0313'}}, {{'\u1f52'}, {'\u03a5', '\u0313', '\u0300'}}, {{'\u1f54'}, {'\u03a5', '\u0313', '\u0301'}}, {{'\u1f56'}, {'\u03a5', '\u0313', '\u0342'}}, {{'\u1f80'}, {'\u1f08', '\u0399'}}, {{'\u1f81'}, {'\u1f09', '\u0399'}}, {{'\u1f82'}, {'\u1f0a', '\u0399'}}, {{'\u1f83'}, {'\u1f0b', '\u0399'}}, {{'\u1f84'}, {'\u1f0c', '\u0399'}}, {{'\u1f85'}, {'\u1f0d', '\u0399'}}, {{'\u1f86'}, {'\u1f0e', '\u0399'}}, {{'\u1f87'}, {'\u1f0f', '\u0399'}}, {{'\u1f88'}, {'\u1f08', '\u0399'}}, {{'\u1f89'}, {'\u1f09', '\u0399'}}, {{'\u1f8a'}, {'\u1f0a', '\u0399'}}, {{'\u1f8b'}, {'\u1f0b', '\u0399'}}, {{'\u1f8c'}, {'\u1f0c', '\u0399'}}, {{'\u1f8d'}, {'\u1f0d', '\u0399'}}, {{'\u1f8e'}, {'\u1f0e', '\u0399'}}, {{'\u1f8f'}, {'\u1f0f', '\u0399'}}, {{'\u1f90'}, {'\u1f28', '\u0399'}}, {{'\u1f91'}, {'\u1f29', '\u0399'}}, {{'\u1f92'}, {'\u1f2a', '\u0399'}}, {{'\u1f93'}, {'\u1f2b', '\u0399'}}, {{'\u1f94'}, {'\u1f2c', '\u0399'}}, {{'\u1f95'}, {'\u1f2d', '\u0399'}}, {{'\u1f96'}, {'\u1f2e', '\u0399'}}, {{'\u1f97'}, {'\u1f2f', '\u0399'}}, {{'\u1f98'}, {'\u1f28', '\u0399'}}, {{'\u1f99'}, {'\u1f29', '\u0399'}}, {{'\u1f9a'}, {'\u1f2a', '\u0399'}}, {{'\u1f9b'}, {'\u1f2b', '\u0399'}}, {{'\u1f9c'}, {'\u1f2c', '\u0399'}}, {{'\u1f9d'}, {'\u1f2d', '\u0399'}}, {{'\u1f9e'}, {'\u1f2e', '\u0399'}}, {{'\u1f9f'}, {'\u1f2f', '\u0399'}}, {{'\u1fa0'}, {'\u1f68', '\u0399'}}, {{'\u1fa1'}, {'\u1f69', '\u0399'}}, {{'\u1fa2'}, {'\u1f6a', '\u0399'}}, {{'\u1fa3'}, {'\u1f6b', '\u0399'}}, {{'\u1fa4'}, {'\u1f6c', '\u0399'}}, {{'\u1fa5'}, {'\u1f6d', '\u0399'}}, {{'\u1fa6'}, {'\u1f6e', '\u0399'}}, {{'\u1fa7'}, {'\u1f6f', '\u0399'}}, {{'\u1fa8'}, {'\u1f68', '\u0399'}}, {{'\u1fa9'}, {'\u1f69', '\u0399'}}, {{'\u1faa'}, {'\u1f6a', '\u0399'}}, {{'\u1fab'}, {'\u1f6b', '\u0399'}}, {{'\u1fac'}, {'\u1f6c', '\u0399'}}, {{'\u1fad'}, {'\u1f6d', '\u0399'}}, {{'\u1fae'}, {'\u1f6e', '\u0399'}}, {{'\u1faf'}, {'\u1f6f', '\u0399'}}, {{'\u1fb2'}, {'\u1fba', '\u0399'}}, {{'\u1fb3'}, {'\u0391', '\u0399'}}, {{'\u1fb4'}, {'\u0386', '\u0399'}}, {{'\u1fb6'}, {'\u0391', '\u0342'}}, {{'\u1fb7'}, {'\u0391', '\u0342', '\u0399'}}, {{'\u1fbc'}, {'\u0391', '\u0399'}}, {{'\u1fc2'}, {'\u1fca', '\u0399'}}, {{'\u1fc3'}, {'\u0397', '\u0399'}}, {{'\u1fc4'}, {'\u0389', '\u0399'}}, {{'\u1fc6'}, {'\u0397', '\u0342'}}, {{'\u1fc7'}, {'\u0397', '\u0342', '\u0399'}}, {{'\u1fcc'}, {'\u0397', '\u0399'}}, {{'\u1fd2'}, {'\u0399', '\u0308', '\u0300'}}, {{'\u1fd3'}, {'\u0399', '\u0308', '\u0301'}}, {{'\u1fd6'}, {'\u0399', '\u0342'}}, {{'\u1fd7'}, {'\u0399', '\u0308', '\u0342'}}, {{'\u1fe2'}, {'\u03a5', '\u0308', '\u0300'}}, {{'\u1fe3'}, {'\u03a5', '\u0308', '\u0301'}}, {{'\u1fe4'}, {'\u03a1', '\u0313'}}, {{'\u1fe6'}, {'\u03a5', '\u0342'}}, {{'\u1fe7'}, {'\u03a5', '\u0308', '\u0342'}}, {{'\u1ff2'}, {'\u1ffa', '\u0399'}}, {{'\u1ff3'}, {'\u03a9', '\u0399'}}, {{'\u1ff4'}, {'\u038f', '\u0399'}}, {{'\u1ff6'}, {'\u03a9', '\u0342'}}, {{'\u1ff7'}, {'\u03a9', '\u0342', '\u0399'}}, {{'\u1ffc'}, {'\u03a9', '\u0399'}}, {{'\ufb00'}, {'F', 'F'}}, {{'\ufb01'}, {'F', 'I'}}, {{'\ufb02'}, {'F', 'L'}}, {{'\ufb03'}, {'F', 'F', 'I'}}, {{'\ufb04'}, {'F', 'F', 'L'}}, {{'\ufb05'}, {'S', 'T'}}, {{'\ufb06'}, {'S', 'T'}}, {{'\ufb13'}, {'\u0544', '\u0546'}}, {{'\ufb14'}, {'\u0544', '\u0535'}}, {{'\ufb15'}, {'\u0544', '\u053b'}}, {{'\ufb16'}, {'\u054e', '\u0546'}}, {{'\ufb17'}, {'\u0544', '\u053d'}}};
        {
            char[] data = A_DATA.toCharArray();
            if (!$assertionsDisabled && !(data.length == (748 * 2))) throw new AssertionError();
            int i = 0;
            int j = 0;
            while (i < (748 * 2)) {
                int entry = data[i++] << 16;
                A[j++] = entry | data[i++];
            }
        }
    }
}
