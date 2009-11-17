package java.util.regex;

import sun.security.action.GetPropertyAction;

public class PatternSyntaxException extends IllegalArgumentException {
    private final String desc;
    private final String pattern;
    private final int index;
    
    public PatternSyntaxException(String desc, String regex, int index) {
        
        this.desc = desc;
        this.pattern = regex;
        this.index = index;
    }
    
    public int getIndex() {
        return index;
    }
    
    public String getDescription() {
        return desc;
    }
    
    public String getPattern() {
        return pattern;
    }
    private static String nl;
    static {
        nl = (String)(String)java.security.AccessController.doPrivileged(new GetPropertyAction("line.separator"));
    }
    
    public String getMessage() {
        String nl = System.getProperty("line.separator");
        StringBuffer sb = new StringBuffer();
        sb.append(desc);
        if (index >= 0) {
            sb.append(" near index ");
            sb.append(index);
        }
        sb.append(nl);
        sb.append(pattern);
        if (index >= 0) {
            sb.append(nl);
            for (int i = 0; i < index; i++) sb.append(' ');
            sb.append('^');
        }
        return sb.toString();
    }
}
