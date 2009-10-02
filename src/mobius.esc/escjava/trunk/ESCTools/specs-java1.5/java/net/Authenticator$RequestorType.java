package java.net;

public enum Authenticator$RequestorType extends Enum<Authenticator$RequestorType> {
    /*public static final*/ PROXY /* = new Authenticator$RequestorType("PROXY", 0) */,
    /*public static final*/ SERVER /* = new Authenticator$RequestorType("SERVER", 1) */;
    /*synthetic*/ private static final Authenticator$RequestorType[] $VALUES = new Authenticator$RequestorType[]{Authenticator$RequestorType.PROXY, Authenticator$RequestorType.SERVER};
    
    public static final Authenticator$RequestorType[] values() {
        return (Authenticator$RequestorType[])$VALUES.clone();
    }
    
    public static Authenticator$RequestorType valueOf(String name) {
        return (Authenticator$RequestorType)Enum.valueOf(Authenticator.RequestorType.class, name);
    }
    
    private Authenticator$RequestorType(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
