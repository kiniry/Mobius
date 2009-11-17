package java.util;

class Formatter$Conversion {
    
    private Formatter$Conversion() {
        
    }
    static final char DECIMAL_INTEGER = 'd';
    static final char OCTAL_INTEGER = 'o';
    static final char HEXADECIMAL_INTEGER = 'x';
    static final char HEXADECIMAL_INTEGER_UPPER = 'X';
    static final char SCIENTIFIC = 'e';
    static final char SCIENTIFIC_UPPER = 'E';
    static final char GENERAL = 'g';
    static final char GENERAL_UPPER = 'G';
    static final char DECIMAL_FLOAT = 'f';
    static final char HEXADECIMAL_FLOAT = 'a';
    static final char HEXADECIMAL_FLOAT_UPPER = 'A';
    static final char CHARACTER = 'c';
    static final char CHARACTER_UPPER = 'C';
    static final char DATE_TIME = 't';
    static final char DATE_TIME_UPPER = 'T';
    static final char BOOLEAN = 'b';
    static final char BOOLEAN_UPPER = 'B';
    static final char STRING = 's';
    static final char STRING_UPPER = 'S';
    static final char HASHCODE = 'h';
    static final char HASHCODE_UPPER = 'H';
    static final char LINE_SEPARATOR = 'n';
    static final char PERCENT_SIGN = '%';
    
    static boolean isValid(char c) {
        return (isGeneral(c) || isInteger(c) || isFloat(c) || isText(c) || c == 't' || c == 'c');
    }
    
    static boolean isGeneral(char c) {
        switch (c) {
        case BOOLEAN: 
        
        case BOOLEAN_UPPER: 
        
        case STRING: 
        
        case STRING_UPPER: 
        
        case HASHCODE: 
        
        case HASHCODE_UPPER: 
            return true;
        
        default: 
            return false;
        
        }
    }
    
    static boolean isInteger(char c) {
        switch (c) {
        case DECIMAL_INTEGER: 
        
        case OCTAL_INTEGER: 
        
        case HEXADECIMAL_INTEGER: 
        
        case HEXADECIMAL_INTEGER_UPPER: 
            return true;
        
        default: 
            return false;
        
        }
    }
    
    static boolean isFloat(char c) {
        switch (c) {
        case SCIENTIFIC: 
        
        case SCIENTIFIC_UPPER: 
        
        case GENERAL: 
        
        case GENERAL_UPPER: 
        
        case DECIMAL_FLOAT: 
        
        case HEXADECIMAL_FLOAT: 
        
        case HEXADECIMAL_FLOAT_UPPER: 
            return true;
        
        default: 
            return false;
        
        }
    }
    
    static boolean isText(char c) {
        switch (c) {
        case LINE_SEPARATOR: 
        
        case PERCENT_SIGN: 
            return true;
        
        default: 
            return false;
        
        }
    }
}
