package java.lang;

class ConditionalSpecialCasing$Entry {
    int ch;
    char[] lower;
    char[] upper;
    String lang;
    int condition;
    
    ConditionalSpecialCasing$Entry(int ch, char[] lower, char[] upper, String lang, int condition) {
        
        this.ch = ch;
        this.lower = lower;
        this.upper = upper;
        this.lang = lang;
        this.condition = condition;
    }
    
    int getCodePoint() {
        return ch;
    }
    
    char[] getLowerCase() {
        return lower;
    }
    
    char[] getUpperCase() {
        return upper;
    }
    
    String getLanguage() {
        return lang;
    }
    
    int getCondition() {
        return condition;
    }
}
