///******************************************************************************
//* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
//*------------------------------------------------------------------------------
//* Name: RunnableWithError.java
//*
//********************************************************************************
//* Warnings/Remarks:
//*******************************************************************************/
package jack.plugin;

/**
 * This class manages errors that can occur during an action.
 * 
 * @author A. Requet
 */
public class RunnableWithError {

    public RunnableWithError() {
           succeeded = true;
    }
    
    private boolean succeeded;
    private String errorDescription;
	private String errorDetails;

    /**
     * Return true if the JPO generation succeeded, false otherwise.
     * In case where the method return false, a description of the error
     * can be found in @see getErrorDescription()
     */
    public boolean hasSucceeded()
    {
        return succeeded;
    }

	/**
	 * Indicates if a detailed description of the error is available.
	 * 
	 * @return true if a detailed description of the error is available,
	 *          false otherwise.
	 */    
    public boolean hasDetails()
    {
    	return errorDetails != null;
    }
    
    /**
     * Return a description of the error in case where hasSucceeded return false.
     */
    public String getErrorDescription()
    {
        return errorDescription;
    }

	/**
	 * Returns detail for the error, if available. return null if no details
	 * are available.
	 */
	public String getErrorDetails()
	{
		return errorDetails;
	}
    
    /**
     * Indicates that an error has occured.
     * 
     * @param description description of the error. Should not be null.
     */
    protected void setError(String description)
    {
        succeeded = false;
        errorDescription = description;
        errorDetails = null;
    }

	/**
	 * Indicates that an error has occured.
	 * 
	 * @param description descriptio of the error.
	 * @param detail additional details on the error.
	 */
	protected void setError(String description, String detail)
	{
		succeeded = false;
		errorDescription = description;
		errorDetails = detail;
	}
}
