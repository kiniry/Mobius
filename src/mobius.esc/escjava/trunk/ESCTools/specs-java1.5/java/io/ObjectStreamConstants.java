package java.io;

public interface ObjectStreamConstants {
    static final short STREAM_MAGIC = (short)44269;
    static final short STREAM_VERSION = 5;
    static final byte TC_BASE = 112;
    static final byte TC_NULL = (byte)112;
    static final byte TC_REFERENCE = (byte)113;
    static final byte TC_CLASSDESC = (byte)114;
    static final byte TC_OBJECT = (byte)115;
    static final byte TC_STRING = (byte)116;
    static final byte TC_ARRAY = (byte)117;
    static final byte TC_CLASS = (byte)118;
    static final byte TC_BLOCKDATA = (byte)119;
    static final byte TC_ENDBLOCKDATA = (byte)120;
    static final byte TC_RESET = (byte)121;
    static final byte TC_BLOCKDATALONG = (byte)122;
    static final byte TC_EXCEPTION = (byte)123;
    static final byte TC_LONGSTRING = (byte)124;
    static final byte TC_PROXYCLASSDESC = (byte)125;
    static final byte TC_ENUM = (byte)126;
    static final byte TC_MAX = (byte)126;
    static final int baseWireHandle = 8257536;
    static final byte SC_WRITE_METHOD = 1;
    static final byte SC_BLOCK_DATA = 8;
    static final byte SC_SERIALIZABLE = 2;
    static final byte SC_EXTERNALIZABLE = 4;
    static final byte SC_ENUM = 16;
    static final SerializablePermission SUBSTITUTION_PERMISSION = new SerializablePermission("enableSubstitution");
    static final SerializablePermission SUBCLASS_IMPLEMENTATION_PERMISSION = new SerializablePermission("enableSubclassImplementation");
    public static final int PROTOCOL_VERSION_1 = 1;
    public static final int PROTOCOL_VERSION_2 = 2;
}
