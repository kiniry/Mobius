package java.sql;

public interface Clob {
    
    long length() throws SQLException;
    
    String getSubString(long pos, int length) throws SQLException;
    
    java.io.Reader getCharacterStream() throws SQLException;
    
    java.io.InputStream getAsciiStream() throws SQLException;
    
    long position(String searchstr, long start) throws SQLException;
    
    long position(Clob searchstr, long start) throws SQLException;
    
    int setString(long pos, String str) throws SQLException;
    
    int setString(long pos, String str, int offset, int len) throws SQLException;
    
    java.io.OutputStream setAsciiStream(long pos) throws SQLException;
    
    java.io.Writer setCharacterStream(long pos) throws SQLException;
    
    void truncate(long len) throws SQLException;
}
