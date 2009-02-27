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
public abstract class LoggerFactoryImpl {

  /**
   * 
   */
  public String logPath = "logs/";
  /**
   * 
   */
  public String logSuffix = ".log";
  
  /**
   * @param c
   * @return
   */
  abstract public Logger getClassLogger(Class<?> c);
}
