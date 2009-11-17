package java.util;

class Formatter$DateTime {
    
    private Formatter$DateTime() {
        
    }
    static final char HOUR_OF_DAY_0 = 'H';
    static final char HOUR_0 = 'I';
    static final char HOUR_OF_DAY = 'k';
    static final char HOUR = 'l';
    static final char MINUTE = 'M';
    static final char NANOSECOND = 'N';
    static final char MILLISECOND = 'L';
    static final char MILLISECOND_SINCE_EPOCH = 'Q';
    static final char AM_PM = 'p';
    static final char SECONDS_SINCE_EPOCH = 's';
    static final char SECOND = 'S';
    static final char TIME = 'T';
    static final char ZONE_NUMERIC = 'z';
    static final char ZONE = 'Z';
    static final char NAME_OF_DAY_ABBREV = 'a';
    static final char NAME_OF_DAY = 'A';
    static final char NAME_OF_MONTH_ABBREV = 'b';
    static final char NAME_OF_MONTH = 'B';
    static final char CENTURY = 'C';
    static final char DAY_OF_MONTH_0 = 'd';
    static final char DAY_OF_MONTH = 'e';
    static final char NAME_OF_MONTH_ABBREV_X = 'h';
    static final char DAY_OF_YEAR = 'j';
    static final char MONTH = 'm';
    static final char YEAR_2 = 'y';
    static final char YEAR_4 = 'Y';
    static final char TIME_12_HOUR = 'r';
    static final char TIME_24_HOUR = 'R';
    static final char DATE_TIME = 'c';
    static final char DATE = 'D';
    static final char ISO_STANDARD_DATE = 'F';
    
    static boolean isValid(char c) {
        switch (c) {
        case HOUR_OF_DAY_0: 
        
        case HOUR_0: 
        
        case HOUR_OF_DAY: 
        
        case HOUR: 
        
        case MINUTE: 
        
        case NANOSECOND: 
        
        case MILLISECOND: 
        
        case MILLISECOND_SINCE_EPOCH: 
        
        case AM_PM: 
        
        case SECONDS_SINCE_EPOCH: 
        
        case SECOND: 
        
        case TIME: 
        
        case ZONE_NUMERIC: 
        
        case ZONE: 
        
        case NAME_OF_DAY_ABBREV: 
        
        case NAME_OF_DAY: 
        
        case NAME_OF_MONTH_ABBREV: 
        
        case NAME_OF_MONTH: 
        
        case CENTURY: 
        
        case DAY_OF_MONTH_0: 
        
        case DAY_OF_MONTH: 
        
        case NAME_OF_MONTH_ABBREV_X: 
        
        case DAY_OF_YEAR: 
        
        case MONTH: 
        
        case YEAR_2: 
        
        case YEAR_4: 
        
        case TIME_12_HOUR: 
        
        case TIME_24_HOUR: 
        
        case DATE_TIME: 
        
        case DATE: 
        
        case ISO_STANDARD_DATE: 
            return true;
        
        default: 
            return false;
        
        }
    }
}
