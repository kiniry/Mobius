package java.util.regex;

abstract class Pattern$JavaTypeClass extends Pattern$Node {
    
    Pattern$JavaTypeClass() {
        
    }
    
    Pattern$Node dup(boolean not) {
        Pattern$Node duplicate = null;
        try {
            duplicate = (Pattern$Node)(Pattern$Node)this.getClass().newInstance();
        } catch (InstantiationException ie) {
            throw new Error("Cannot instantiate node");
        } catch (IllegalAccessException iae) {
            throw new Error("Cannot instantiate node");
        }
        if (not) return new Pattern$Not(duplicate); else return duplicate;
    }
    
    abstract boolean isProperty(int ch);
    
    boolean match(Matcher matcher, int i, CharSequence seq) {
        if (i >= matcher.to) {
            matcher.hitEnd = true;
            return false;
        }
        int c = Character.codePointAt(seq, i);
        return (isProperty(c) && next.match(matcher, i + Character.charCount(c), seq));
    }
    
    boolean study(Pattern$TreeInfo info) {
        info.minLength++;
        info.maxLength++;
        return next.study(info);
    }
}
