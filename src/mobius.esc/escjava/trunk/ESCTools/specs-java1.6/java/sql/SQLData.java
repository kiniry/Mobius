package java.sql;

public interface SQLData {
    
    String getSQLTypeName() throws SQLException;
    
    void readSQL(SQLInput stream, String typeName) throws SQLException;
    
    void writeSQL(SQLOutput stream) throws SQLException;
}
