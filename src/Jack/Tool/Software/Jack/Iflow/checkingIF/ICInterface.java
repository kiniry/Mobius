package checkingIF;

import java.util.ArrayList;
import java.util.Iterator;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.verifier.structurals.ExceptionHandler;

/**
 * An InstructionContext offers convenient access
 * to information like control flow successors and
 * such.
 *
 * Created January, 28, 2005
 * @version $Id: ICInterface.java,v 1.2 2005/02/17 12:46:10 lmartini Exp $
 * @author Luca Martini
 */
public interface ICInterface{
    boolean execute(State inState, ArrayList executionPredecessors, CheckingVisitor cv, ExceptionVisitor ev);
    
    /**
     * This method returns the outgoing execution frame situation;
     * therefore <B>it has to be calculated by execute(Frame, ArrayList)
     * first.</B>
     *
     * @see #execute(State, ArrayList, InstConstraintVisitor, ExecutionVisitor)
     */
    State getAfterState(ArrayList executionPredecessors);
	
    /**
     * This method returns the afterstate in case of exception 
     */
    State getExcState();

    /**
     * Returns the InstructionHandle this InstructionContext is wrapped around.
     *
     * @return The InstructionHandle this InstructionContext is wrapped around.
     */
    InstructionHandle getInstruction();

    /**
     * Returns the usual control flow successors.
     * @see #getExceptionHandlers()
     */
    ICInterface[] getSuccessors();

    /**
     * Returns the exception handlers that protect this instruction.
     * They are special control flow successors.
     */
    ExceptionHandler[] getExceptionHandlers();
}
