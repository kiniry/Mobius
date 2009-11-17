package java.sql;

public interface Ref {
    
    String getBaseTypeName() throws SQLException;
    
    Object getObject(java.util.Map map) throws SQLException;
    
    Object getObject() throws SQLException;
    
    void setObject(Object value) throws SQLException;
}
