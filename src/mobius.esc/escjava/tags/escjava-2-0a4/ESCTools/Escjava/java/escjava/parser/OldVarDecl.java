package escjava.parser;

import javafe.ast.*;

public class OldVarDecl extends javafe.ast.LocalVarDecl {


    public static OldVarDecl make(/*@ non_null */ Identifier id,
			/*@ non_null */ Type type,
			int locId,
			/*@ non_null */ VarInit init,
			int locAssignOp
			) {
	OldVarDecl result = new OldVarDecl();
	result.modifiers = Modifiers.NONE;
	result.pmodifiers = null;
	result.id = id;
	result.type = type;
	result.locId = locId;
	result.init = init;
	result.locAssignOp = locAssignOp;
	return result;
    }

}
