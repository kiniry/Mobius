package java.sql;

import java.math.BigDecimal;
import java.util.Calendar;

public interface CallableStatement extends PreparedStatement {
    
    void registerOutParameter(int parameterIndex, int sqlType) throws SQLException;
    
    void registerOutParameter(int parameterIndex, int sqlType, int scale) throws SQLException;
    
    boolean wasNull() throws SQLException;
    
    String getString(int parameterIndex) throws SQLException;
    
    boolean getBoolean(int parameterIndex) throws SQLException;
    
    byte getByte(int parameterIndex) throws SQLException;
    
    short getShort(int parameterIndex) throws SQLException;
    
    int getInt(int parameterIndex) throws SQLException;
    
    long getLong(int parameterIndex) throws SQLException;
    
    float getFloat(int parameterIndex) throws SQLException;
    
    double getDouble(int parameterIndex) throws SQLException;
    
    
    BigDecimal getBigDecimal(int parameterIndex, int scale) throws SQLException;
    
    byte[] getBytes(int parameterIndex) throws SQLException;
    
    java.sql.Date getDate(int parameterIndex) throws SQLException;
    
    java.sql.Time getTime(int parameterIndex) throws SQLException;
    
    java.sql.Timestamp getTimestamp(int parameterIndex) throws SQLException;
    
    Object getObject(int parameterIndex) throws SQLException;
    
    BigDecimal getBigDecimal(int parameterIndex) throws SQLException;
    
    Object getObject(int i, java.util.Map map) throws SQLException;
    
    Ref getRef(int i) throws SQLException;
    
    Blob getBlob(int i) throws SQLException;
    
    Clob getClob(int i) throws SQLException;
    
    Array getArray(int i) throws SQLException;
    
    java.sql.Date getDate(int parameterIndex, Calendar cal) throws SQLException;
    
    java.sql.Time getTime(int parameterIndex, Calendar cal) throws SQLException;
    
    java.sql.Timestamp getTimestamp(int parameterIndex, Calendar cal) throws SQLException;
    
    void registerOutParameter(int paramIndex, int sqlType, String typeName) throws SQLException;
    
    void registerOutParameter(String parameterName, int sqlType) throws SQLException;
    
    void registerOutParameter(String parameterName, int sqlType, int scale) throws SQLException;
    
    void registerOutParameter(String parameterName, int sqlType, String typeName) throws SQLException;
    
    java.net.URL getURL(int parameterIndex) throws SQLException;
    
    void setURL(String parameterName, java.net.URL val) throws SQLException;
    
    void setNull(String parameterName, int sqlType) throws SQLException;
    
    void setBoolean(String parameterName, boolean x) throws SQLException;
    
    void setByte(String parameterName, byte x) throws SQLException;
    
    void setShort(String parameterName, short x) throws SQLException;
    
    void setInt(String parameterName, int x) throws SQLException;
    
    void setLong(String parameterName, long x) throws SQLException;
    
    void setFloat(String parameterName, float x) throws SQLException;
    
    void setDouble(String parameterName, double x) throws SQLException;
    
    void setBigDecimal(String parameterName, BigDecimal x) throws SQLException;
    
    void setString(String parameterName, String x) throws SQLException;
    
    void setBytes(String parameterName, byte[] x) throws SQLException;
    
    void setDate(String parameterName, java.sql.Date x) throws SQLException;
    
    void setTime(String parameterName, java.sql.Time x) throws SQLException;
    
    void setTimestamp(String parameterName, java.sql.Timestamp x) throws SQLException;
    
    void setAsciiStream(String parameterName, java.io.InputStream x, int length) throws SQLException;
    
    void setBinaryStream(String parameterName, java.io.InputStream x, int length) throws SQLException;
    
    void setObject(String parameterName, Object x, int targetSqlType, int scale) throws SQLException;
    
    void setObject(String parameterName, Object x, int targetSqlType) throws SQLException;
    
    void setObject(String parameterName, Object x) throws SQLException;
    
    void setCharacterStream(String parameterName, java.io.Reader reader, int length) throws SQLException;
    
    void setDate(String parameterName, java.sql.Date x, Calendar cal) throws SQLException;
    
    void setTime(String parameterName, java.sql.Time x, Calendar cal) throws SQLException;
    
    void setTimestamp(String parameterName, java.sql.Timestamp x, Calendar cal) throws SQLException;
    
    void setNull(String parameterName, int sqlType, String typeName) throws SQLException;
    
    String getString(String parameterName) throws SQLException;
    
    boolean getBoolean(String parameterName) throws SQLException;
    
    byte getByte(String parameterName) throws SQLException;
    
    short getShort(String parameterName) throws SQLException;
    
    int getInt(String parameterName) throws SQLException;
    
    long getLong(String parameterName) throws SQLException;
    
    float getFloat(String parameterName) throws SQLException;
    
    double getDouble(String parameterName) throws SQLException;
    
    byte[] getBytes(String parameterName) throws SQLException;
    
    java.sql.Date getDate(String parameterName) throws SQLException;
    
    java.sql.Time getTime(String parameterName) throws SQLException;
    
    java.sql.Timestamp getTimestamp(String parameterName) throws SQLException;
    
    Object getObject(String parameterName) throws SQLException;
    
    BigDecimal getBigDecimal(String parameterName) throws SQLException;
    
    Object getObject(String parameterName, java.util.Map map) throws SQLException;
    
    Ref getRef(String parameterName) throws SQLException;
    
    Blob getBlob(String parameterName) throws SQLException;
    
    Clob getClob(String parameterName) throws SQLException;
    
    Array getArray(String parameterName) throws SQLException;
    
    java.sql.Date getDate(String parameterName, Calendar cal) throws SQLException;
    
    java.sql.Time getTime(String parameterName, Calendar cal) throws SQLException;
    
    java.sql.Timestamp getTimestamp(String parameterName, Calendar cal) throws SQLException;
    
    java.net.URL getURL(String parameterName) throws SQLException;
}
