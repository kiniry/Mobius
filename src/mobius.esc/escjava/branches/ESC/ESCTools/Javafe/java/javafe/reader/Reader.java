/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.reader;


import javafe.ast.CompilationUnit;
import javafe.genericfile.*;


/**
 ** A Reader is an object that reads then parses a GenericFile,
 ** returning a CompilationUnit.  Iff problems arise, errors will be
 ** reported via javafe.util.ErrorSet and then null will be returned.<p>
 **
 ** Readers may or may not cache the results of their reading.<p>
 **
 ** The class CachedReader can be used to turn a noncaching Reader into
 ** a caching Reader.<p>
 **/

abstract public class Reader {

    /***************************************************
     *                                                 *
     * Reading:					       *
     *                                                 *
     ***************************************************/

    /**
     ** Attempt to read and parse a CompilationUnit from target.
     ** Any errors encountered are reported via javafe.util.ErrorSet.
     ** Null is returned iff an error was encountered.<p>
     **
     **
     ** By default, we attempt to read only a spec (e.g., specOnly is set
     ** in the resulting CompilationUnit) to save time.  If avoidSpec is
     ** true, we attempt to return a non-spec, although this may not
     ** always be possible.<p>
     **
     **
     ** The result of this function may or may not be cached.<p>
     ** If it is cached, then only the value of avoidSpec used the first
     ** time a given file is read is used.  This may result in a spec
     ** being returned unnecessarily when avoidSpec is true.<p>
     **
     ** Target must be non-null.<p>
     **/
    //@ requires target!=null
    abstract public CompilationUnit read(GenericFile target,
				         boolean avoidSpec);
}
