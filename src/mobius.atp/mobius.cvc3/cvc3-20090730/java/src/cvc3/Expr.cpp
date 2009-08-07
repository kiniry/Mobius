#include <expr.h>
#include <theory_array.h>
#include <theory_arith.h>
#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniEquals
(JNIEnv* env, jclass, jobject jexpr1, jobject jexpr2)
{
  try {
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return *expr1 == *expr2;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Expr_jniToString
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJava(env, expr->toString());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_Expr_jniPrint
(JNIEnv* env, jclass, jobject jexpr, jstring jlang, jboolean jdagify)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    string lang(toCpp(env, jlang));
    bool dagify(jdagify);
    //expr->print(toCppInputLanguage(env, lang), dagify);
    expr->pprintnodag();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_Expr_jniHash
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->hash();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsFalse
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isFalse();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsTrue
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isTrue();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsBoolConst
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isBoolConst();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsVar
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isVar();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsBoundVar
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isBoundVar();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsString
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isString();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsClosure
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isClosure();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsQuantifier
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isQuantifier();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsLambda
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isLambda();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsApply
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isApply();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsSymbol
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isSymbol();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsTheorem
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isTheorem();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsType
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isType();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsTerm
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isTerm();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsAtomic
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isAtomic();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsAtomicFormula
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isAtomicFormula();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsAbsAtomicFormula
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isAbsAtomicFormula();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsLiteral
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isLiteral();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsAbsLiteral
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isAbsLiteral();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsBoolConnective
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isBoolConnective();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsPropAtom
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isPropAtom();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsPropLiteral
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isPropLiteral();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsEq
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isEq();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsNot
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isNot();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsAnd
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isAnd();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsOr
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isOr();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsITE
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isITE();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsIff
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isIff();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsImpl
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isImpl();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsXor
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isXor();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsForall
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isForall();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsExists
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isExists();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsRational
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isRational();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsUminus
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == UMINUS;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsPlus
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == PLUS;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsMinus
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == MINUS;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsMult
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == MULT;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsPow
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == POW;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsDivide
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == DIVIDE;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsLt
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == LT;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsLe
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == LE;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsGt
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == GT;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsGe
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == GE;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsSkolem
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isSkolem();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsRead
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == READ;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsWrite
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getKind() == WRITE;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Expr_jniGetName
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJava(env, expr->getName());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Expr_jniGetUid
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJava(env, expr->getUid());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Expr_jniGetString
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJava(env, expr->getString());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_Expr_jniGetVars
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJavaVConstRef(env, expr->getVars());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Expr_jniGetExistential
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_const_ref<Expr>(env, &expr->getExistential());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_Expr_jniGetBoundIndex
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->getBoundIndex();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Expr_jniGetBody
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_const_ref<Expr>(env, &expr->getBody());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Expr_jniGetRational
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_const_ref<Rational>(env, &expr->getRational());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Expr_jniGetTheorem
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_const_ref<Theorem>(env, &expr->getTheorem());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Expr_jniGetType
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy<Type>(env, expr->getType());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Expr_jniMkOp
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy<Op>(env, expr->mkOp());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Expr_jniGetOp
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy<Op>(env, expr->getOp());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Expr_jniIsNull
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->isNull();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_Expr_jniArity
(JNIEnv* env, jclass, jobject jexpr)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return expr->arity();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Expr_jniGetChild
(JNIEnv* env, jclass, jobject jexpr, jint ji)
{
  try {
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    int i(ji);
    return embed_const_ref<Expr>(env, &((*expr)[ji]));
  } catch (const Exception& e) { toJava(env, e); };
}

