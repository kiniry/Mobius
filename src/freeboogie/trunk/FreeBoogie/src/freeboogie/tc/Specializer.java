package freeboogie.tc;

import freeboogie.ast.Transformer;

/**
 * Modifies explicit specializations given "desired" types for
 * certain AST nodes, if possible. It also needs as input the
 * implicit specializations performed by a TypeChecker on the
 * given AST.
 */
class Specializer extends Transformer {
}
