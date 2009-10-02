package java.sql;

public interface Blob {
    
    long length() throws SQLException;
    
    byte[] getBytes(long pos, int length) throws SQLException;
    
    java.io.InputStream getBinaryStream() throws SQLException;
    
    long position(byte[] pattern, long start) throws SQLException;
    
    long position(Blob pattern, long start) throws SQLException;
    
    int setBytes(long pos, byte[] bytes) throws SQLException;
    
    int setBytes(long pos, byte[] bytes, int offset, int len) throws SQLException;
    
    java.io.OutputStream setBinaryStream(long pos) throws SQLException;
    
    void truncate(long len) throws SQLException;
}
