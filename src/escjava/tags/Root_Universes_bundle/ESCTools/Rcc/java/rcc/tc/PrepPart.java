/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import javafe.ast.FieldDeclVec;
import javafe.ast.MethodDeclVec;

class PrepPart extends Object {
    FieldDeclVec fields;

    MethodDeclVec methods;

    public PrepPart(FieldDeclVec fields, MethodDeclVec methods) {
        this.fields = fields;
        this.methods = methods;
    }
}
