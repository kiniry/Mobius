package Mock;

import jml2bml.bytecode.BmlAnnotation;
import jml2bml.bytecode.BytecodeUtils;
import jml2bml.bytecode.Location;

import com.sun.source.tree.Tree;

public class MockBytecodeUtils implements BytecodeUtils {

	@Override
	public Location findLocation(Tree node) {
		return new Location();
	}

	@Override
	public void insertAnnotation(BmlAnnotation annotation) {
		System.out.println("inserting annotation " + annotation.getAnnotation());

	}

}
