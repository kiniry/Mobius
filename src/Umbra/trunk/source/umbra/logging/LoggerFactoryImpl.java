/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.logging;

import java.util.logging.Logger;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class LoggerFactoryImpl {

  /**
   * relative path for logs produced by loggers from this factory
   */
  protected String logPath;
  
  /**
   * suffix for log files 
   */
  protected String logSuffix = ".log";
  
  LoggerFactoryImpl(String logPath) {
    this.logPath = logPath;
  }
  
  /**
   * @return path where logs go
   */
  public String getLogPath() {
    return logPath;
  }
  
  /**
   * @param c class for which the logger is created 
   * @return new logger
   */
  abstract public Logger getClassLogger(Class<?> c);
  
}
