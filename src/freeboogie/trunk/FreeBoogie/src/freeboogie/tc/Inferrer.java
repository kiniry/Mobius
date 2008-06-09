package freeboogie.tc;

/**
 * Given an AST, it infers types for the lowest nodes that were
 * given an errType by the typechecker. This is based on applying
 * top-down heuristics (e.g., if the AST contains a==b then
 * this gets translated into the type equation typeof(a)==typeof(b)).
 */
class Inferrer {
}
