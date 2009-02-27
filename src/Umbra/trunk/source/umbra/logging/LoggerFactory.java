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
 * @version a-01
 *
 */
public class LoggerFactory {

  private enum Mode {DEVELOPMENT, DEBUG, PRODUCTION};
  
  private static Mode mode = Mode.DEVELOPMENT;
  private static LoggerFactoryImpl loggerFactoryImpl = getRightImpl();

  private static LoggerFactoryImpl getRightImpl() {
    switch (mode) {
      case DEVELOPMENT: 
        return new LoggerFactoryDevelopmentImpl();
      case DEBUG: 
        return new LoggerFactoryDevelopmentImpl();
      case PRODUCTION: 
        return new LoggerFactoryDevelopmentImpl();
    }
    return null;
  }
  
  /**
   * @param newMode
   */
  public static void setMode(final Mode newMode) {
    if (newMode != mode) {
      mode = newMode;
      loggerFactoryImpl = getRightImpl();
    }
  }
  
  /**
   * @return mode the factory is currently in
   */
  public static Mode getMode() {
    return mode;
  }
  
  /**
   * @param c class we create logger for
   * @return new instance of logger with formatters and handlers set by
   * currently used factory implementation
   */
  public static Logger getClassLogger(final Class<?> c) {
    return loggerFactoryImpl.getClassLogger(c);
  }
  
}
