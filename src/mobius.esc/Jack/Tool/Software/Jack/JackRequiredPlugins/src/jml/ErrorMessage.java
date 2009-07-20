package jml;

/**
 * Simple class representing error messages.
 */
public class ErrorMessage
{
    public ErrorMessage(String err, int line, int col)
    {
	this.line = line;
	this.column = col;
	this.message = err;
    }

    /** 
     * The line in the source code corresponding to the error message. 
     */
    public int line;

    /**
     * The column in the source code corresponding to the error message.
     */
    public int column;

    /**
     * The error message.
     */
    public String message;
}
