/*
 * This file is part of the Esc/Java plugin project.
 * Copyright 2004 David R. Cok
 * 
 * Created on Jul 30, 2004
 */
package escjava.plugin;

import org.eclipse.core.resources.IResource;

/**
 * This interface represents listeners. These listeners want
 * to know about one event: an error report from EscJava,
 * via the method escjavaFailed.
 * 
 * @author David R. Cok
 */
public interface IEscjavaListener {

  /** A severity constant indicating an illegal condition. */
  int ERROR = 2;
  
  /** A severity constant indicating an ok but problematic condition. */
  int WARNING = 1;
  
  /** A severity constant indicating an informational message. */
  int INFO = 0;
  

  /**
   * This method represents the event in which there was an error during
   * Escjava checking.
   * 
   * @param resource The resource in which the error occured
   * @param file The file in which the error occured
   * @param lineNumber The line number where the error happened
   * @param offset The character position (0-based) from the beginning 
   * of the file where the error begins
   * @param length The number of characters to highlight
   * @param errorMessage A message explaining the type of error
   * @param severity The severity of the error (using one of the 
   * error severity constants defined in this class)
   */
  void escjavaFailed(IResource resource, 
      String file, int lineNumber, 
      int offset, int length,
      String errorMessage, int severity);

}
