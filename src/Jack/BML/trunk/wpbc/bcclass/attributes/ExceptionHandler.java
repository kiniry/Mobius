/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcclass.attributes;


import formula.Formula;

import bcexpression.javatype.JavaObjectType;


public class ExceptionHandler {
	int start_pc;
	int end_pc;
	JavaObjectType catchType;
	int handler_pc;

	// calculated only ones - i.e. the algorithm rubs only once
	//through the subgraph of the exception handler
	private Formula wp;

	ExceptionHandler(
		int _start_pc,
		int _end_pc,
		JavaObjectType _exc,
		int _handler_pc) {
		start_pc = _start_pc;
		end_pc = _end_pc;
		catchType = _exc;
		handler_pc = _handler_pc;
	}
	/**
	 * @return Returns the end_pc.
	 */
	public int getEndPC() {
		return end_pc;
	}
	/**
	 * @return Returns the exc.
	 */
	public JavaObjectType getCatchType() {
		return catchType;
	}
	/**
	 * @return Returns the handler_pc.
	 */
	public int getHandlerPC() {
		return handler_pc;
	}
	/**
	 * @return Returns the start_pc.
	 */
	public int getStartPC() {
		return start_pc;
	}

	public String toString() {
		String str =
			" startPC: "
				+ start_pc
				+ "; endPC: "
				+ end_pc
				+ "; catchType: "
				+ catchType.getSignature()
				+ "; handlerPc: "
				+ handler_pc;
		return str;
	}
}