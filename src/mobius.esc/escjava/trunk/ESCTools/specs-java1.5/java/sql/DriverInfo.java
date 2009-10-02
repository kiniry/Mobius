package java.sql;

class DriverInfo {
    
    DriverInfo() {
        
    }
    Driver driver;
    Class driverClass;
    String driverClassName;
    
    public String toString() {
        return ("driver[className=" + driverClassName + "," + driver + "]");
    }
}
