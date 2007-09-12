package annot.bcclass.attributes;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantDouble;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantFloat;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantInterfaceMethodref;
import org.apache.bcel.classfile.ConstantLong;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;


/**
 * @author mpavlova
 * 
 *represents a class invariant 
 */
public class SecondConstantPool implements BCAttribute {

	int constant_pool_count;
	Constant[] constant_pool;

	 /**
	   * Initialize instance from file data.
	   *
	   * @param file Input stream
	   * @throws IOException
	   */
	static ConstantClass ConstantClass(DataInputStream file) throws IOException
	  {
	    return new ConstantClass(file.readUnsignedShort());
	  }


	 static ConstantFieldref ConstantFieldref(DataInputStream file) throws IOException
	  {
		 return new  ConstantFieldref(file.readUnsignedShort(), file.readUnsignedShort());
		  }
	
	 static ConstantMethodref ConstantMethodref(DataInputStream file) throws IOException
	  {
		 return new  ConstantMethodref(file.readUnsignedShort(), file.readUnsignedShort());
		  }

	 static ConstantInterfaceMethodref ConstantInterfaceMethodref(DataInputStream file) throws IOException
	  {
		 return new  ConstantInterfaceMethodref(file.readUnsignedShort(), file.readUnsignedShort());
		  }
	 
	 static ConstantString ConstantString(DataInputStream file) throws IOException
	  {
		 return new ConstantString((int)file.readUnsignedShort());
	  }

	 
	 static ConstantInteger ConstantInteger(DataInputStream file) throws IOException
	  {
		 return new ConstantInteger(file.readInt());
	  }

	 static ConstantFloat ConstantFloat(DataInputStream file) throws IOException
	  {
		 return new ConstantFloat(file.readFloat());
	  }

	 static ConstantLong ConstantLong(DataInputStream file) throws IOException
	  {
		 return new ConstantLong(file.readLong());
	  }

	 static ConstantDouble ConstantDouble(DataInputStream file) throws IOException
	  {
		 return new ConstantDouble(file.readDouble());
	  }
	 
	 static ConstantNameAndType ConstantNameAndType(DataInputStream file) throws IOException
	  {
		return new  ConstantNameAndType((int)file.readUnsignedShort(), (int)file.readUnsignedShort());
	  }

	 static ConstantUtf8 ConstantUtf8(DataInputStream file) throws IOException
	  {
	    return new ConstantUtf8(file.readUTF());
	  }

	 /**
	   * Read one constant from the given file, the type depends on a tag byte.
	   *
	   * @param file Input stream
	   * @return Constant object
	   */
	  static final Constant readConstant(DataInputStream file)
	    throws IOException, ClassFormatException
	  {
	    byte b = file.readByte(); // Read tag byte

	    switch(b) {
	    case Constants.CONSTANT_Class:              return ConstantClass(file);
	    case Constants.CONSTANT_Fieldref:           return ConstantFieldref(file);
	    case Constants.CONSTANT_Methodref:          return ConstantMethodref(file);
	    case Constants.CONSTANT_InterfaceMethodref: return ConstantInterfaceMethodref(file);
	    case Constants.CONSTANT_String:             return ConstantString(file);
	    case Constants.CONSTANT_Integer:            return ConstantInteger(file);
	    case Constants.CONSTANT_Float:              return ConstantFloat(file);
	    case Constants.CONSTANT_Long:               return ConstantLong(file);
	    case Constants.CONSTANT_Double:             return ConstantDouble(file);
	    case Constants.CONSTANT_NameAndType:        return  ConstantNameAndType(file);
	    case Constants.CONSTANT_Utf8:               return ConstantUtf8(file);
	    default:
	      throw new ClassFormatException("Invalid byte tag in constant pool: " + b);
	    }
	  }

	  /**
	   * Read constants from given file stream.
	   *
	   * @param file Input stream
	   * @throws IOException
	   * @throws ClassFormatException
	   */
	public SecondConstantPool(DataInputStream file) throws IOException, ClassFormatException
	  {
	    byte tag;

	    constant_pool_count = file.readUnsignedShort();
	    constant_pool       = new Constant[constant_pool_count];

	    /* constant_pool[0] is unused by the compiler and may be used freely
	     * by the implementation.
	     */
	    for(int i=0; i < constant_pool_count; i++) {
	      constant_pool[i] = readConstant(file);
//	      DataOutputStream dos = new DataOutputStream(System.out);
//	      constant_pool[i].dump(dos);
//	      System.out.println("   "+constant_pool[i].toString());

	      /* Quote from the JVM specification:
	       * "All eight byte constants take up two spots in the constant pool.
	       * If this is the n'th byte in the constant pool, then the next item
	       * will be numbered n+2"
	       *
	       * Thus we have to increment the index counter.
	       */
	      tag = constant_pool[i].getTag();
	      if((tag == Constants.CONSTANT_Double) || (tag == Constants.CONSTANT_Long))
	        i++;
	    }
	  }


	public Constant getConstant_pool(int index) {
		return constant_pool[index];
	}

	public int getConstant_pool_count() {
		return constant_pool_count;
	}
}
