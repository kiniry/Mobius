package java.beans;

class Statement$1 implements ExceptionListener {
    
    Statement$1() {
        
    }
    
    public void exceptionThrown(Exception e) {
        System.err.println(e);
        System.err.println("Continuing ...");
    }
}
