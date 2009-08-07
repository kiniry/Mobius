#include <expr_op.h>
#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Op_jniEquals
(JNIEnv* env, jclass, jobject jop1, jobject jop2)
{
  try {
    const Op* op1 = unembed_const<Op>(env, jop1);
    const Op* op2 = unembed_const<Op>(env, jop2);
    return *op1 == *op2;
     
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Op_jniToString
(JNIEnv* env, jclass, jobject jop)
{
  try {
    const Op* op = unembed_const<Op>(env, jop);
    return toJava(env, op->toString());
     
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Op_jniGetExpr
(JNIEnv* env, jclass, jobject jop)
{
  try {
    const Op* op = unembed_const<Op>(env, jop);
    return embed_const_ref<Expr>(env, &op->getExpr());
  } catch (const Exception& e) { toJava(env, e); };
}

