package java.sql;

public interface SQLOutput {
    
    void writeString(String x) throws SQLException;
    
    void writeBoolean(boolean x) throws SQLException;
    
    void writeByte(byte x) throws SQLException;
    
    void writeShort(short x) throws SQLException;
    
    void writeInt(int x) throws SQLException;
    
    void writeLong(long x) throws SQLException;
    
    void writeFloat(float x) throws SQLException;
    
    void writeDouble(double x) throws SQLException;
    
    void writeBigDecimal(java.math.BigDecimal x) throws SQLException;
    
    void writeBytes(byte[] x) throws SQLException;
    
    void writeDate(java.sql.Date x) throws SQLException;
    
    void writeTime(java.sql.Time x) throws SQLException;
    
    void writeTimestamp(java.sql.Timestamp x) throws SQLException;
    
    void writeCharacterStream(java.io.Reader x) throws SQLException;
    
    void writeAsciiStream(java.io.InputStream x) throws SQLException;
    
    void writeBinaryStream(java.io.InputStream x) throws SQLException;
    
    void writeObject(SQLData x) throws SQLException;
    
    void writeRef(Ref x) throws SQLException;
    
    void writeBlob(Blob x) throws SQLException;
    
    void writeClob(Clob x) throws SQLException;
    
    void writeStruct(Struct x) throws SQLException;
    
    void writeArray(Array x) throws SQLException;
    
    void writeURL(java.net.URL x) throws SQLException;
}
