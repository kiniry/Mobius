package java.lang.annotation;

public class RetentionPolicy extends Enum {
    public static final RetentionPolicy SOURCE  = new RetentionPolicy("SOURCE", 0);
    public static final RetentionPolicy CLASS  = new RetentionPolicy("CLASS", 1);
    public static final RetentionPolicy RUNTIME  = new RetentionPolicy("RUNTIME", 2);
    /*synthetic*/ private static final RetentionPolicy[] $VALUES = new RetentionPolicy[]{RetentionPolicy.SOURCE, RetentionPolicy.CLASS, RetentionPolicy.RUNTIME};
    
    public static final RetentionPolicy[] values() {
        return (RetentionPolicy[])$VALUES.clone();
    }
    
    public static RetentionPolicy valueOf(String name) {
        return (RetentionPolicy)Enum.valueOf(RetentionPolicy.class, name);
    }
    
    private RetentionPolicy(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
