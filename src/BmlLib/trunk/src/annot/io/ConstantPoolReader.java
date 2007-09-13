package annot.io;

import java.io.DataInputStream;
import java.io.IOException;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantUtf8;

public class ConstantPoolReader {

	public static Constant readConstant(DataInputStream file)
			throws ReadAttributeException {
		try {
			byte b = file.readByte();
			switch (b) {
			case Constants.CONSTANT_Utf8:
				return new ConstantUtf8(file.readUTF());
			default:
				throw new ReadAttributeException("Unknown constant: " + b);
			}
		} catch (IOException e) {
			throw new ReadAttributeException(
					"Error while reading second constant pool");
		}
	}

}
