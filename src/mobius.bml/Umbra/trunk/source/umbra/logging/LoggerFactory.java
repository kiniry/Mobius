/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.logging;

import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 * @author szymon wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public final class LoggerFactory {

  /**
   *
   * @author szymon wrzyszcz sw237122@students.mimuw.edu.pl)
   * @version a-01
   *
   */
  private enum Mode { DEVELOPMENT, DEBUG, PRODUCTION };

  /**
   *
   */
  private static Mode my_mode = Mode.PRODUCTION;

  /**
   *
   */
  private static LoggerFactoryImpl loggerFactoryImpl = getRightImpl();

  /**
   * forbids creating objects of the class.
   */
  private LoggerFactory() {
  }

  /**
   *
   * @return impl
   */
  private static LoggerFactoryImpl getRightImpl() {
    LoggerFactoryImpl impl = null;
    switch (my_mode) {
      case DEVELOPMENT:
        impl = new LoggerFactoryDevelopmentImpl();
        break;
      case DEBUG:
        impl = new LoggerFactoryDevelopmentImpl();
        break;
      case PRODUCTION:
        impl = new LoggerFactoryDevelopmentImpl();
        break;
      default:
        break;
    }
    return impl;
  }

  /**
   * @param a_new_mode new mode
   */
  public static void setMode(final Mode a_new_mode) {
    if (a_new_mode != my_mode) {
      my_mode = a_new_mode;
      loggerFactoryImpl = getRightImpl();
    }
  }

  /**
   * @return mode the factory is currently in
   */
  public static Mode getMode() {
    return my_mode;
  }

  /**
   * @param a_class class we create logger for
   * @return new instance of logger with formatters and handlers set by
   * currently used factory implementation
   */
  public static Logger getClassLogger(final Class < ? > a_class) {
    return loggerFactoryImpl.getClassLogger(a_class);
  }

  /**
   * @param a_name name of the logger
   * @return new logger
   */
  public static Logger getDefaultLogger(final String a_name) {
    return loggerFactoryImpl.getDefaultLogger(a_name);
  }

  /**
   * @param a_name name of the logger
   * @return new logger
   */
  public static Logger getMockUpLogger(final String a_name) {
    final Logger logger = loggerFactoryImpl.getDefaultLogger(
              "[" + a_name + "]");
    logger.setLevel(Level.ALL);
    for (Handler h : logger.getHandlers()) {
      h.setLevel(Level.ALL);
    }
    return logger;
  }

}
