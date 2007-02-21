package b2bpl.bpl.transformation;

import b2bpl.bpl.ast.BPLProgram;


public interface BPLTransformator {

  BPLProgram transform(BPLProgram program);
}
