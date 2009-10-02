package java.net;

public enum Proxy$Type extends Enum<Proxy$Type> {
    /*public static final*/ DIRECT /* = new Proxy$Type("DIRECT", 0) */,
    /*public static final*/ HTTP /* = new Proxy$Type("HTTP", 1) */,
    /*public static final*/ SOCKS /* = new Proxy$Type("SOCKS", 2) */;
    /*synthetic*/ private static final Proxy$Type[] $VALUES = new Proxy$Type[]{Proxy$Type.DIRECT, Proxy$Type.HTTP, Proxy$Type.SOCKS};
    
    public static final Proxy$Type[] values() {
        return (Proxy$Type[])$VALUES.clone();
    }
    
    public static Proxy$Type valueOf(String name) {
        return (Proxy$Type)Enum.valueOf(Proxy.Type.class, name);
    }
    
    private Proxy$Type(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
