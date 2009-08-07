#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_ExprManager_jniGetInputLanguage
(JNIEnv* env, jclass, jobject jexprManager)
{
  try {
    const ExprManager* exprManager = unembed_const<ExprManager>(env, jexprManager);
    return toJava(env, exprManager->getInputLang());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_ExprManager_jniGetOutputLanguage
(JNIEnv* env, jclass, jobject jexprManager)
{
  try {
    const ExprManager* exprManager = unembed_const<ExprManager>(env, jexprManager);
    return toJava(env, exprManager->getOutputLang());
  } catch (const Exception& e) { toJava(env, e); };
}

