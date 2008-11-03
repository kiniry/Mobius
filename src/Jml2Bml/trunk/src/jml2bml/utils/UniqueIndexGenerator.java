/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.utils;

/**
 *
 * @author Jedrek (fulara@mimuw.edu.pl)
 *
 * Generates unique index (for bounded variables)
 * @version 0-1
 *
 */
public final class UniqueIndexGenerator {

  /**
   * Previous index value.
   */
  private static int index;

  /**
   * Hidden constructor.
   */
  private UniqueIndexGenerator() {
  }

  /**
   * Generates new index.
   * @return generated index
   */
  public static int getNext() {
    index++;
    return index;
  }

}
