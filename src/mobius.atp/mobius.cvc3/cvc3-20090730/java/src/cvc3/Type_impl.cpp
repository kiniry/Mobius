INCLUDE: "type.h"


DEFINITION: Java_cvc3_Type_jniIsNull
jboolean c Type type
return type->isNull();

DEFINITION: Java_cvc3_Type_jniIsBool
jboolean c Type type
return type->isBool();

DEFINITION: Java_cvc3_Type_jniIsSubtype
jboolean c Type type
return type->isSubtype();

DEFINITION: Java_cvc3_Type_jniIsFunction
jboolean c Type type
return type->isFunction();



DEFINITION: Java_cvc3_Type_jniGetExpr
jobject c Type type
return embed_const_ref<Expr>(env, &type->getExpr());

DEFINITION: Java_cvc3_Type_jniArity
jint c Type type
return type->arity();

DEFINITION: Java_cvc3_Type_jniGetChild
jobject c Type type n int i
return embed_copy<Type>(env, (*type)[i]);




DEFINITION: Java_cvc3_Type_jniEquals
jboolean c Type type1 c Type type2
return *type1 == *type2;

DEFINITION: Java_cvc3_Type_jniToString
jstring c Type type
return toJava(env, type->toString());

