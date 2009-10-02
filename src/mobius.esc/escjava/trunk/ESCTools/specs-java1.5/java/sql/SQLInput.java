package java.sql;

public interface SQLInput {
    
    String readString() throws SQLException;
    
    boolean readBoolean() throws SQLException;
    
    byte readByte() throws SQLException;
    
    short readShort() throws SQLException;
    
    int readInt() throws SQLException;
    
    long readLong() throws SQLException;
    
    float readFloat() throws SQLException;
    
    double readDouble() throws SQLException;
    
    java.math.BigDecimal readBigDecimal() throws SQLException;
    
    byte[] readBytes() throws SQLException;
    
    java.sql.Date readDate() throws SQLException;
    
    java.sql.Time readTime() throws SQLException;
    
    java.sql.Timestamp readTimestamp() throws SQLException;
    
    java.io.Reader readCharacterStream() throws SQLException;
    
    java.io.InputStream readAsciiStream() throws SQLException;
    
    java.io.InputStream readBinaryStream() throws SQLException;
    
    Object readObject() throws SQLException;
    
    Ref readRef() throws SQLException;
    
    Blob readBlob() throws SQLException;
    
    Clob readClob() throws SQLException;
    
    Array readArray() throws SQLException;
    
    boolean wasNull() throws SQLException;
    
    java.net.URL readURL() throws SQLException;
}
