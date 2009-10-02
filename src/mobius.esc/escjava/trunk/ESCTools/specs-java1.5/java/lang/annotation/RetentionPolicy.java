package java.lang.annotation;

public enum RetentionPolicy extends Enum<RetentionPolicy> {
    /*public static final*/ SOURCE /* = new RetentionPolicy("SOURCE", 0) */,
    /*public static final*/ CLASS /* = new RetentionPolicy("CLASS", 1) */,
    /*public static final*/ RUNTIME /* = new RetentionPolicy("RUNTIME", 2) */;
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
