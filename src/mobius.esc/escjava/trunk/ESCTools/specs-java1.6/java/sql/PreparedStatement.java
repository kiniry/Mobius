package java.sql;

import java.math.BigDecimal;
import java.util.Calendar;

public interface PreparedStatement extends Statement {
    
    ResultSet executeQuery() throws SQLException;
    
    int executeUpdate() throws SQLException;
    
    void setNull(int parameterIndex, int sqlType) throws SQLException;
    
    void setBoolean(int parameterIndex, boolean x) throws SQLException;
    
    void setByte(int parameterIndex, byte x) throws SQLException;
    
    void setShort(int parameterIndex, short x) throws SQLException;
    
    void setInt(int parameterIndex, int x) throws SQLException;
    
    void setLong(int parameterIndex, long x) throws SQLException;
    
    void setFloat(int parameterIndex, float x) throws SQLException;
    
    void setDouble(int parameterIndex, double x) throws SQLException;
    
    void setBigDecimal(int parameterIndex, BigDecimal x) throws SQLException;
    
    void setString(int parameterIndex, String x) throws SQLException;
    
    void setBytes(int parameterIndex, byte[] x) throws SQLException;
    
    void setDate(int parameterIndex, java.sql.Date x) throws SQLException;
    
    void setTime(int parameterIndex, java.sql.Time x) throws SQLException;
    
    void setTimestamp(int parameterIndex, java.sql.Timestamp x) throws SQLException;
    
    void setAsciiStream(int parameterIndex, java.io.InputStream x, int length) throws SQLException;
    
    
    void setUnicodeStream(int parameterIndex, java.io.InputStream x, int length) throws SQLException;
    
    void setBinaryStream(int parameterIndex, java.io.InputStream x, int length) throws SQLException;
    
    void clearParameters() throws SQLException;
    
    void setObject(int parameterIndex, Object x, int targetSqlType, int scale) throws SQLException;
    
    void setObject(int parameterIndex, Object x, int targetSqlType) throws SQLException;
    
    void setObject(int parameterIndex, Object x) throws SQLException;
    
    boolean execute() throws SQLException;
    
    void addBatch() throws SQLException;
    
    void setCharacterStream(int parameterIndex, java.io.Reader reader, int length) throws SQLException;
    
    void setRef(int i, Ref x) throws SQLException;
    
    void setBlob(int i, Blob x) throws SQLException;
    
    void setClob(int i, Clob x) throws SQLException;
    
    void setArray(int i, Array x) throws SQLException;
    
    ResultSetMetaData getMetaData() throws SQLException;
    
    void setDate(int parameterIndex, java.sql.Date x, Calendar cal) throws SQLException;
    
    void setTime(int parameterIndex, java.sql.Time x, Calendar cal) throws SQLException;
    
    void setTimestamp(int parameterIndex, java.sql.Timestamp x, Calendar cal) throws SQLException;
    
    void setNull(int paramIndex, int sqlType, String typeName) throws SQLException;
    
    void setURL(int parameterIndex, java.net.URL x) throws SQLException;
    
    ParameterMetaData getParameterMetaData() throws SQLException;
}
