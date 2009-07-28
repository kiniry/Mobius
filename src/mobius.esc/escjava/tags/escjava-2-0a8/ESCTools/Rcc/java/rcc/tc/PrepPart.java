/* Copyright 2000, 2001, Compaq Computer Corporation */

package rcc.tc;

import java.util.Hashtable;

import javafe.ast.*;
import javafe.util.*;

import javafe.ast.*;
import javafe.tc.*; 
import javafe.util.Location;


class PrepPart extends Object  {
  FieldDeclVec fields;
  MethodDeclVec methods;
  
  public  PrepPart(FieldDeclVec fields, MethodDeclVec method) {
    this.fields = fields;
    this.methods = methods;
  }
  
}
