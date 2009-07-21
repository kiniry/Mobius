package b2bpl.bytecode;

import java.util.ArrayList;
import java.util.List;

import b2bpl.bytecode.analysis.StackFrame;
import b2bpl.bytecode.bml.ast.BMLAssertStatement;
import b2bpl.bytecode.bml.ast.BMLAssumeStatement;
import b2bpl.bytecode.bml.ast.BMLLoopSpecification;
import b2bpl.bytecode.instructions.Instruction;


public final class InstructionHandle {

  private Instruction instruction;

  private InstructionHandle next;

  private InstructionHandle previous;
  
  private int index = -1;

  private List<BMLAssertStatement> assertions =
    new ArrayList<BMLAssertStatement>();

  private List<BMLAssumeStatement> assumptions =
    new ArrayList<BMLAssumeStatement>();

  private List<BMLLoopSpecification> loopSpecifications =
    new ArrayList<BMLLoopSpecification>();

  private StackFrame frame;

  private boolean isThisInitialized;

  public Instruction getInstruction() {
    return instruction;
  }

  public void setInstruction(Instruction instruction) {
    this.instruction = instruction;
  }

  public InstructionHandle getNext() {
    return next;
  }

  void setNext(InstructionHandle next) {
    this.next = next;
  }

  public InstructionHandle getPrevious() {
    return previous;
  }

  void setPrevious(InstructionHandle previous) {
    this.previous = previous;
  }

  public int getIndex() {
    return index;
  }

  void setIndex(int index) {
    this.index = index;
  }

  public List<BMLAssertStatement> getAssertions() {
    return assertions;
  }

  public void addAssertion(BMLAssertStatement assertion) {
    assertions.add(assertion);
  }

  public List<BMLAssumeStatement> getAssumptions() {
    return assumptions;
  }

  public void addAssumption(BMLAssumeStatement assumption) {
    assumptions.add(assumption);
  }

  public List<BMLLoopSpecification> getLoopSpecifications() {
    return loopSpecifications;
  }

  public void addLoopSpecification(BMLLoopSpecification loopSpecification) {
    loopSpecifications.add(loopSpecification);
  }

  public StackFrame getFrame() {
    return frame;
  }

  public void setFrame(StackFrame frame) {
    this.frame = frame;
  }

  public boolean isThisInitialized() {
    return isThisInitialized;
  }

  public void setThisInitialized(boolean isThisInitialized) {
    this.isThisInitialized = isThisInitialized;
  }

  public void accept(IInstructionVisitor visitor) {
    if (instruction != null) {
      instruction.accept(visitor);
    }
  }

  public String toString() {
    StringBuffer sb = new StringBuffer();

    sb.append((index == -1) ? "??" : String.valueOf(index));
    sb.append(": ");
    sb.append((instruction == null) ? "??" : instruction.toString());

    return sb.toString();
  }
}
