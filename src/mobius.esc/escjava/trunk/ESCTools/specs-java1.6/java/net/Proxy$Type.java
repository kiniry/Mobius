package java.net;

public class Proxy$Type extends Enum {
    public static final Proxy$Type DIRECT  = new Proxy$Type("DIRECT", 0);
    public static final Proxy$Type HTTP  = new Proxy$Type("HTTP", 1);
    public static final Proxy$Type SOCKS  = new Proxy$Type("SOCKS", 2);
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
