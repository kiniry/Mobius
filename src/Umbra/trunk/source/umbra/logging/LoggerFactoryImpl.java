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
   * relative path for logs produced by loggers from this factory.
   */
  private String my_logPath;

  /**
   * suffix for log files.
   */
  private String my_logSuffix = ".log";

  /**
   *
   * @param a_log_path path to file we log to
   */
  LoggerFactoryImpl(final String a_log_path) {
    this.my_logPath = a_log_path;
  }

  /**
   * @return path where logs go
   */
  public String getLogPath() {
    return my_logPath;
  }
  
  /**
   *
   * @return
   */
  public String getLogSuffix() {
    return my_logSuffix;
  }

  /**
   * @param a_class class for which the logger is created.
   * @return new logger
   */
  public abstract Logger getClassLogger(Class < ? > a_class);

  /**
   * @param a_name  logger name
   * @return new logger with default settings
   */
  public Logger getDefaultLogger(final String a_name) {
    return Logger.getLogger(a_name);
  }
}
