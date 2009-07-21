package b2bpl.bpl.transformation;

import b2bpl.bpl.ast.BPLProgram;


/**
 * Simple interface to be implemented by every class which would like to
 * contribute to the set of transformations performed on the BoogiePL program
 * resulting from the core translation of bytecode classes to BoogiePL.
 *
 * <p>
 * Every {@code BPLTransformator} gets the current BoogiePL program as input and
 * it returns a new BoogiePL program on which an arbitrary set of
 * transformations may have been performed.
 * </p>
 *
 * @author Ovidio Mallo
 */
public interface IBPLTransformator {

  /**
   * Performs an arbitrary set of transformations on the given {@code program}
   * and returns the new, transformed BoogiePL program.
   *
   * @param program  The input BoogiePL program to which to apply the
   *                 transformations.
   * @return         The new, transformed BoogiePL program.
   */
  BPLProgram transform(BPLProgram program);
}
