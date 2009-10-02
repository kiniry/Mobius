package javax.xml.parsers;

class FactoryFinder$ConfigurationError extends Error {
    private Exception exception;
    
    FactoryFinder$ConfigurationError(String msg, Exception x) {
        super(msg);
        this.exception = x;
    }
    
    Exception getException() {
        return exception;
    }
}
