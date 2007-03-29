package b2bpl.bytecode.bml;

import b2bpl.bytecode.bml.ast.BMLArrayElementStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayAllStoreRef;
import b2bpl.bytecode.bml.ast.BMLArrayRangeStoreRef;
import b2bpl.bytecode.bml.ast.BMLEverythingStoreRef;
import b2bpl.bytecode.bml.ast.BMLFieldAccessStoreRef;
import b2bpl.bytecode.bml.ast.BMLFieldStoreRef;
import b2bpl.bytecode.bml.ast.BMLLocalVariableStoreRef;
import b2bpl.bytecode.bml.ast.BMLNothingStoreRef;
import b2bpl.bytecode.bml.ast.BMLThisStoreRef;


/**
 * Visitor for BML store references.
 *
 * @param <R>  Type parameter specifying the return type declared on all the
 *             methods of the visitor.
 *
 * @author Ovidio Mallo
 */
public interface BMLStoreRefVisitor<R> {

  R visitEverythingStoreRef(BMLEverythingStoreRef storeRef);

  R visitNothingStoreRef(BMLNothingStoreRef storeRef);

  R visitThisStoreRef(BMLThisStoreRef storeRef);

  R visitLocalVariableStoreRef(BMLLocalVariableStoreRef storeRef);

  R visitFieldStoreRef(BMLFieldStoreRef storeRef);

  R visitFieldAccessStoreRef(BMLFieldAccessStoreRef storeRef);

  R visitArrayElementStoreRef(BMLArrayElementStoreRef storeRef);

  R visitArrayAllStoreRef(BMLArrayAllStoreRef storeRef);

  R visitArrayRangeStoreRef(BMLArrayRangeStoreRef storeRef);
}
