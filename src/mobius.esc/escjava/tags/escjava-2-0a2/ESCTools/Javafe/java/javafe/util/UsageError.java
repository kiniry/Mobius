/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.util;

/**
 * A UsageError is thrown when the command-line arguments are
 * invalid.
 */

public class UsageError extends java.lang.Exception
{
    /**
     * Create a <code>UsageError</code> exception.
     */
    public UsageError(String s) {
	super(s);
    }
}
