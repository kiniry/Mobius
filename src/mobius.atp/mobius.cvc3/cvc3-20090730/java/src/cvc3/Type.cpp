#include "type.h"
#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Type_jniIsNull
(JNIEnv* env, jclass, jobject jtype)
{
  try {
    const Type* type = unembed_const<Type>(env, jtype);
    return type->isNull();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Type_jniIsBool
(JNIEnv* env, jclass, jobject jtype)
{
  try {
    const Type* type = unembed_const<Type>(env, jtype);
    return type->isBool();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Type_jniIsSubtype
(JNIEnv* env, jclass, jobject jtype)
{
  try {
    const Type* type = unembed_const<Type>(env, jtype);
    return type->isSubtype();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Type_jniIsFunction
(JNIEnv* env, jclass, jobject jtype)
{
  try {
    const Type* type = unembed_const<Type>(env, jtype);
    return type->isFunction();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Type_jniGetExpr
(JNIEnv* env, jclass, jobject jtype)
{
  try {
    const Type* type = unembed_const<Type>(env, jtype);
    return embed_const_ref<Expr>(env, &type->getExpr());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_Type_jniArity
(JNIEnv* env, jclass, jobject jtype)
{
  try {
    const Type* type = unembed_const<Type>(env, jtype);
    return type->arity();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Type_jniGetChild
(JNIEnv* env, jclass, jobject jtype, jint ji)
{
  try {
    const Type* type = unembed_const<Type>(env, jtype);
    int i(ji);
    return embed_copy<Type>(env, (*type)[i]);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Type_jniEquals
(JNIEnv* env, jclass, jobject jtype1, jobject jtype2)
{
  try {
    const Type* type1 = unembed_const<Type>(env, jtype1);
    const Type* type2 = unembed_const<Type>(env, jtype2);
    return *type1 == *type2;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Type_jniToString
(JNIEnv* env, jclass, jobject jtype)
{
  try {
    const Type* type = unembed_const<Type>(env, jtype);
    return toJava(env, type->toString());
  } catch (const Exception& e) { toJava(env, e); };
}

