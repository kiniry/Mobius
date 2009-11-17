package java.text;

import java.io.Serializable;

public abstract class Format implements Serializable, Cloneable {
    
    public Format() {
        
    }
    private static final long serialVersionUID = -299282585814624189L;
    
    public final String format(Object obj) {
        return format(obj, new StringBuffer(), new FieldPosition(0)).toString();
    }
    
    public abstract StringBuffer format(Object obj, StringBuffer toAppendTo, FieldPosition pos);
    
    public AttributedCharacterIterator formatToCharacterIterator(Object obj) {
        return createAttributedCharacterIterator(format(obj));
    }
    
    public abstract Object parseObject(String source, ParsePosition pos);
    
    public Object parseObject(String source) throws ParseException {
        ParsePosition pos = new ParsePosition(0);
        Object result = parseObject(source, pos);
        if (pos.index == 0) {
            throw new ParseException("Format.parseObject(String) failed", pos.errorIndex);
        }
        return result;
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            return null;
        }
    }
    
    AttributedCharacterIterator createAttributedCharacterIterator(String s) {
        AttributedString as = new AttributedString(s);
        return as.getIterator();
    }
    
    AttributedCharacterIterator createAttributedCharacterIterator(AttributedCharacterIterator[] iterators) {
        AttributedString as = new AttributedString(iterators);
        return as.getIterator();
    }
    
    AttributedCharacterIterator createAttributedCharacterIterator(String string, AttributedCharacterIterator$Attribute key, Object value) {
        AttributedString as = new AttributedString(string);
        as.addAttribute(key, value);
        return as.getIterator();
    }
    
    AttributedCharacterIterator createAttributedCharacterIterator(AttributedCharacterIterator iterator, AttributedCharacterIterator$Attribute key, Object value) {
        AttributedString as = new AttributedString(iterator);
        as.addAttribute(key, value);
        return as.getIterator();
    }
    {
    }
    {
    }
}
