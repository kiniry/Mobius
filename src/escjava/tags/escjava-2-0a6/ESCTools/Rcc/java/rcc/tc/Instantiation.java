/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import rcc.ast.*;
import javafe.ast.*;
import javafe.tc.*;

public class Instantiation {
		public javafe.tc.TypeSig sig;
		public ExprVec expressions;
		public javafe.tc.TypeSig instantiation;
		public Instantiation(javafe.tc.TypeSig sig,
												 ExprVec expressions,
												 javafe.tc.TypeSig instantiation) {
				this.sig = sig;
				this.expressions = expressions;
				this.instantiation = instantiation;
		}
		
}
