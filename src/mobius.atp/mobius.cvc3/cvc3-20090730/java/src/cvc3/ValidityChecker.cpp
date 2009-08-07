#include <sstream>
#include <theory_arith.h>
#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniCreate1
(JNIEnv* env, jclass)
{
  try {
    return embed_own<ValidityChecker>(env, VCL::create());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniCreate2
(JNIEnv* env, jclass, jobject jflags)
{
  try {
    const CLFlags* flags = unembed_const<CLFlags>(env, jflags);
    return embed_own<ValidityChecker>(env, VCL::create(*flags));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniCreateFlags
(JNIEnv* env, jclass)
{
  try {
    return embed_copy(env, ValidityChecker::createFlags());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetFlags
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    const ValidityChecker* vc = unembed_const<ValidityChecker>(env, jvc);
    return embed_mut_ref(env, &vc->getFlags());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniBoolType
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->boolType());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRealType
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->realType());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniIntType
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->intType());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniSubrangeType
(JNIEnv* env, jclass, jobject jvc, jobject jl, jobject jr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* l = unembed_const<Expr>(env, jl);
    const Expr* r = unembed_const<Expr>(env, jr);
    return embed_copy(env, vc->subrangeType(*l, *r));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniSubtypeType
(JNIEnv* env, jclass, jobject jvc, jobject jpred, jobject jwitness)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* pred = unembed_const<Expr>(env, jpred);
    const Expr* witness = unembed_const<Expr>(env, jwitness);
    return embed_copy(env, vc->subtypeType(*pred, *witness));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniTupleType1
(JNIEnv* env, jclass, jobject jvc, jobject jtype0, jobject jtype1)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Type* type0 = unembed_const<Type>(env, jtype0);
    const Type* type1 = unembed_const<Type>(env, jtype1);
    return embed_copy(env, vc->tupleType(*type0, *type1));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniTupleType2
(JNIEnv* env, jclass, jobject jvc, jobject jtype0, jobject jtype1, jobject jtype2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Type* type0 = unembed_const<Type>(env, jtype0);
    const Type* type1 = unembed_const<Type>(env, jtype1);
    const Type* type2 = unembed_const<Type>(env, jtype2);
    return embed_copy(env, vc->tupleType(*type0, *type1, *type2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniTupleType3
(JNIEnv* env, jclass, jobject jvc, jobjectArray jtypes)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Type> types(toCppV<Type>(env, jtypes));
    return embed_copy(env, vc->tupleType(types));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecordType1
(JNIEnv* env, jclass, jobject jvc, jstring jfield, jobject jtype)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string field(toCpp(env, jfield));
    const Type* type = unembed_const<Type>(env, jtype);
    return embed_copy(env, vc->recordType(field, *type));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecordType2
(JNIEnv* env, jclass, jobject jvc, jstring jfield0, jobject jtype0, jstring jfield1, jobject jtype1)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string field0(toCpp(env, jfield0));
    const Type* type0 = unembed_const<Type>(env, jtype0);
    string field1(toCpp(env, jfield1));
    const Type* type1 = unembed_const<Type>(env, jtype1);
    return embed_copy(env, vc->recordType(field0, *type0, field1, *type1));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecordType3
(JNIEnv* env, jclass, jobject jvc, jstring jfield0, jobject jtype0, jstring jfield1, jobject jtype1, jstring jfield2, jobject jtype2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string field0(toCpp(env, jfield0));
    const Type* type0 = unembed_const<Type>(env, jtype0);
    string field1(toCpp(env, jfield1));
    const Type* type1 = unembed_const<Type>(env, jtype1);
    string field2(toCpp(env, jfield2));
    const Type* type2 = unembed_const<Type>(env, jtype2);
    return embed_copy(env, vc->recordType(field0, *type0, field1, *type1, field2, *type2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecordType4
(JNIEnv* env, jclass, jobject jvc, jobjectArray jfields, jobjectArray jtypes)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<string> fields(toCppV(env, jfields));
    vector<Type> types(toCppV<Type>(env, jtypes));
    return embed_copy(env, vc->recordType(fields, types));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniDataType1
(JNIEnv* env, jclass, jobject jvc, jstring jname, jstring jconstructor, jobjectArray jselectors, jobjectArray jtypes)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    string constructor(toCpp(env, jconstructor));
    vector<string> selectors(toCppV(env, jselectors));
    vector<Expr> types(toCppV<Expr>(env, jtypes));
    return embed_copy(env, vc->dataType(name, constructor, selectors, types));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniDataType2
(JNIEnv* env, jclass, jobject jvc, jstring jname, jobjectArray jconstructors, jobjectArray jselectors, jobjectArray jtypes)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    vector<string> constructors(toCppV(env, jconstructors));
    vector<vector<string> > selectors(toCppVV(env, jselectors));
    vector<vector<Expr> > types(toCppVV<Expr>(env, jtypes));
    return embed_copy(env, vc->dataType(name, constructors, selectors, types));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniDataType3
(JNIEnv* env, jclass, jobject jvc, jobjectArray jnames, jobjectArray jconstructors, jobjectArray jselectors, jobjectArray jtypes)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<string> names(toCppV(env, jnames));
    vector<vector<string> > constructors(toCppVV(env, jconstructors));
    vector<vector<vector<string> > > selectors(toCppVVV(env, jselectors));
    vector<vector<vector<Expr> > > types(toCppVVV<Expr>(env, jtypes));
    vector<Type> result;
    vc->dataType(names, constructors, selectors, types, result);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniArrayType
(JNIEnv* env, jclass, jobject jvc, jobject jtypeIndex, jobject jtypeData)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Type* typeIndex = unembed_const<Type>(env, jtypeIndex);
    const Type* typeData = unembed_const<Type>(env, jtypeData);
    return embed_copy(env, vc->arrayType(*typeIndex, *typeData));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniBitvecType
(JNIEnv* env, jclass, jobject jvc, jint jn)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    int n(jn);
    return embed_copy(env, vc->bitvecType(n));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniFunType1
(JNIEnv* env, jclass, jobject jvc, jobject jtypeDom, jobject jtypeRange)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Type* typeDom = unembed_const<Type>(env, jtypeDom);
    const Type* typeRange = unembed_const<Type>(env, jtypeRange);
    return embed_copy(env, vc->funType(*typeDom, *typeRange));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniFunType2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jtypeDom, jobject jtypeRange)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Type> typeDom(toCppV<Type>(env, jtypeDom));
    const Type* typeRange = unembed_const<Type>(env, jtypeRange);
    return embed_copy(env, vc->funType(typeDom, *typeRange));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniCreateType1
(JNIEnv* env, jclass, jobject jvc, jstring jtypeName)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string typeName(toCpp(env, jtypeName));
    return embed_copy(env, vc->createType(typeName));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniCreateType2
(JNIEnv* env, jclass, jobject jvc, jstring jtypeName, jobject jtypeDef)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string typeName(toCpp(env, jtypeName));
    const Type* typeDef = unembed_const<Type>(env, jtypeDef);
    return embed_copy(env, vc->createType(typeName, *typeDef));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniLookupType
(JNIEnv* env, jclass, jobject jvc, jstring jtypeName)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string typeName(toCpp(env, jtypeName));
    return embed_copy(env, vc->lookupType(typeName));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetExprManager
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_mut_ref(env, vc->getEM());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNullExpr
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, Expr());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniVarExpr1
(JNIEnv* env, jclass, jobject jvc, jstring jname, jobject jtype)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    const Type* type = unembed_const<Type>(env, jtype);
    return embed_copy(env, vc->varExpr(name, *type));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniVarExpr2
(JNIEnv* env, jclass, jobject jvc, jstring jname, jobject jtype, jobject jdef)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    const Type* type = unembed_const<Type>(env, jtype);
    const Expr* def = unembed_const<Expr>(env, jdef);
    return embed_copy(env, vc->varExpr(name, *type, *def));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniBoundVarExpr
(JNIEnv* env, jclass, jobject jvc, jstring jname, jstring juid, jobject jtype)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    string uid(toCpp(env, juid));
    const Type* type = unembed_const<Type>(env, jtype);
    return embed_copy(env, vc->boundVarExpr(name, uid, *type));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniLookupVar
(JNIEnv* env, jclass, jobject jvc, jstring jname, jobject jtype)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    Type* type = unembed_mut<Type>(env, jtype);
    return embed_copy(env, vc->lookupVar(name, type));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetType
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->getType(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetBaseType1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->getBaseType(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetBaseType2
(JNIEnv* env, jclass, jobject jvc, jobject jtype)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Type* type = unembed_const<Type>(env, jtype);
    return embed_copy(env, vc->getBaseType(*type));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetTypePred
(JNIEnv* env, jclass, jobject jvc, jobject jtype, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Type* type = unembed_const<Type>(env, jtype);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->getTypePred(*type, *expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniStringExpr
(JNIEnv* env, jclass, jobject jvc, jstring jstr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string str(toCpp(env, jstr));
    return embed_copy(env, vc->stringExpr(str));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniIdExpr
(JNIEnv* env, jclass, jobject jvc, jstring jname)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    return embed_copy(env, vc->idExpr(name));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniListExpr1
(JNIEnv* env, jclass, jobject jvc, jobjectArray jkids)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> kids(toCppV<Expr>(env, jkids));
    return embed_copy(env, vc->listExpr(kids));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniListExpr2
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    return embed_copy(env, vc->listExpr(*expr1));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniListExpr3
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->listExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniListExpr4
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2, jobject jexpr3)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    const Expr* expr3 = unembed_const<Expr>(env, jexpr3);
    return embed_copy(env, vc->listExpr(*expr1, *expr2, *expr3));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniListExpr5
(JNIEnv* env, jclass, jobject jvc, jstring jop, jobjectArray jkids)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string op(toCpp(env, jop));
    vector<Expr> kids(toCppV<Expr>(env, jkids));
    return embed_copy(env, vc->listExpr(op, kids));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniListExpr6
(JNIEnv* env, jclass, jobject jvc, jstring jop, jobject jexpr1)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string op(toCpp(env, jop));
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    return embed_copy(env, vc->listExpr(op, *expr1));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniListExpr7
(JNIEnv* env, jclass, jobject jvc, jstring jop, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string op(toCpp(env, jop));
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->listExpr(op, *expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniListExpr8
(JNIEnv* env, jclass, jobject jvc, jstring jop, jobject jexpr1, jobject jexpr2, jobject jexpr3)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string op(toCpp(env, jop));
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    const Expr* expr3 = unembed_const<Expr>(env, jexpr3);
    return embed_copy(env, vc->listExpr(op, *expr1, *expr2, *expr3));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniParseExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->parseExpr(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniParseType
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->parseType(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniImportExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->importExpr(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniImportType
(JNIEnv* env, jclass, jobject jvc, jobject jtype)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Type* type = unembed_const<Type>(env, jtype);
    return embed_copy(env, vc->importType(*type));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniTrueExpr
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy<Expr>(env, vc->trueExpr());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniFalseExpr
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy<Expr>(env, vc->falseExpr());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNotExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->notExpr(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniAndExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->andExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniAndExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jchildren)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> children(toCppV<Expr>(env, jchildren));
    return embed_copy(env, vc->andExpr(children));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniOrExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->orExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniOrExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jchildren)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> children(toCppV<Expr>(env, jchildren));
    return embed_copy(env, vc->orExpr(children));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniImpliesExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->impliesExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniIffExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->iffExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniEqExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->eqExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniDistinctExpr
(JNIEnv* env, jclass, jobject jvc, jobjectArray jchildren)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> children(toCppV<Expr>(env, jchildren));
    return embed_copy(env, vc->distinctExpr(children));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniIteExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2, jobject jexpr3)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    const Expr* expr3 = unembed_const<Expr>(env, jexpr3);
    return embed_copy(env, vc->iteExpr(*expr1, *expr2, *expr3));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniCreateOp1
(JNIEnv* env, jclass, jobject jvc, jstring jname, jobject jtype)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    const Type* type = unembed_const<Type>(env, jtype);
    return embed_copy(env, vc->createOp(name, *type));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniCreateOp2
(JNIEnv* env, jclass, jobject jvc, jstring jname, jobject jtype, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string name(toCpp(env, jname));
    const Type* type = unembed_const<Type>(env, jtype);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->createOp(name, *type, *expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniEqOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(EQ));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniLtOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(LT));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniLeOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(LE));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGtOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(GT));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGeOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(GE));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniPlusOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(PLUS));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniMinusOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(MINUS));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniMultOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(MULT));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniDivideOp
(JNIEnv* env, jclass)
{
  try {
    return embed_copy<Op>(env, Op(DIVIDE));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniFunExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jop, jobject jexpr1)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Op* op = unembed_const<Op>(env, jop);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    return embed_copy(env, vc->funExpr(*op, *expr1));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniFunExpr2
(JNIEnv* env, jclass, jobject jvc, jobject jop, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Op* op = unembed_const<Op>(env, jop);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->funExpr(*op, *expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniFunExpr3
(JNIEnv* env, jclass, jobject jvc, jobject jop, jobject jexpr1, jobject jexpr2, jobject jexpr3)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Op* op = unembed_const<Op>(env, jop);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    const Expr* expr3 = unembed_const<Expr>(env, jexpr3);
    return embed_copy(env, vc->funExpr(*op, *expr1, *expr2, *expr3));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniFunExpr4
(JNIEnv* env, jclass, jobject jvc, jobject jop, jobjectArray jchildren)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Op* op = unembed_const<Op>(env, jop);
    vector<Expr> children(toCppV<Expr>(env, jchildren));
    return embed_copy(env, vc->funExpr(*op, children));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRatExpr1
(JNIEnv* env, jclass, jobject jvc, jint jn, jint jd)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    int n(jn);
    int d(jd);
    return embed_copy(env, vc->ratExpr(n, d));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRatExpr2
(JNIEnv* env, jclass, jobject jvc, jstring jn, jstring jd, jint jbase)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string n(toCpp(env, jn));
    string d(toCpp(env, jd));
    int base(jbase);
    return embed_copy(env, vc->ratExpr(n, d, base));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRatExpr3
(JNIEnv* env, jclass, jobject jvc, jstring jn, jint jbase)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string n(toCpp(env, jn));
    int base(jbase);
    return embed_copy(env, vc->ratExpr(n, base));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniUminusExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->uminusExpr(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniPlusExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->plusExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniPlusExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jkids)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> kids(toCppV<Expr>(env, jkids));
    return embed_copy(env, vc->plusExpr(kids));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniMinusExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->minusExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniMultExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->multExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniPowExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->powExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniDivideExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->divideExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniLtExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->ltExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniLeExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->leExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGtExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->gtExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGeExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->geExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecordExpr1
(JNIEnv* env, jclass, jobject jvc, jstring jfield, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string field(toCpp(env, jfield));
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->recordExpr(field, *expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecordExpr2
(JNIEnv* env, jclass, jobject jvc, jstring jfield1, jobject jexpr1, jstring jfield2, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string field1(toCpp(env, jfield1));
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    string field2(toCpp(env, jfield2));
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->recordExpr(field1, *expr1, field2, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecordExpr3
(JNIEnv* env, jclass, jobject jvc, jstring jfield1, jobject jexpr1, jstring jfield2, jobject jexpr2, jstring jfield3, jobject jexpr3)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string field1(toCpp(env, jfield1));
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    string field2(toCpp(env, jfield2));
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    string field3(toCpp(env, jfield3));
    const Expr* expr3 = unembed_const<Expr>(env, jexpr3);
    return embed_copy(env, vc->recordExpr(field1, *expr1, field2, *expr2, field2, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecordExpr4
(JNIEnv* env, jclass, jobject jvc, jobjectArray jfields, jobjectArray jexprs)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<string> fields(toCppV(env, jfields));
    vector<Expr> exprs(toCppV<Expr>(env, jexprs));
    return embed_copy(env, vc->recordExpr(fields, exprs));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecSelectExpr
(JNIEnv* env, jclass, jobject jvc, jobject jrecord, jstring jfield)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* record = unembed_const<Expr>(env, jrecord);
    string field(toCpp(env, jfield));
    return embed_copy(env, vc->recSelectExpr(*record, field));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniRecUpdateExpr
(JNIEnv* env, jclass, jobject jvc, jobject jrecord, jstring jfield, jobject jupdate)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* record = unembed_const<Expr>(env, jrecord);
    string field(toCpp(env, jfield));
    const Expr* update = unembed_const<Expr>(env, jupdate);
    return embed_copy(env, vc->recUpdateExpr(*record, field, *update));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniReadExpr
(JNIEnv* env, jclass, jobject jvc, jobject jarray, jobject jindex)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* array = unembed_const<Expr>(env, jarray);
    const Expr* index = unembed_const<Expr>(env, jindex);
    return embed_copy(env, vc->readExpr(*array, *index));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniWriteExpr
(JNIEnv* env, jclass, jobject jvc, jobject jarray, jobject jindex, jobject jvalue)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* array = unembed_const<Expr>(env, jarray);
    const Expr* index = unembed_const<Expr>(env, jindex);
    const Expr* value = unembed_const<Expr>(env, jvalue);
    return embed_copy(env, vc->writeExpr(*array, *index, *value));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVConstExpr1
(JNIEnv* env, jclass, jobject jvc, jstring js, jint jbase)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string s(toCpp(env, js));
    int base(jbase);
    return embed_copy(env, vc->newBVConstExpr(s, jbase));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVConstExpr2
(JNIEnv* env, jclass, jobject jvc, jbooleanArray jbits)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<bool> bits(toCppV(env, jbits));
    return embed_copy(env, vc->newBVConstExpr(bits));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVConstExpr3
(JNIEnv* env, jclass, jobject jvc, jobject jrational, jint jlen)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Rational* rational = unembed_const<Rational>(env, jrational);
    int len(jlen);
    return embed_copy(env, vc->newBVConstExpr(*rational, len));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewConcatExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newConcatExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewConcatExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jkids)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> kids(toCppV<Expr>(env, jkids));
    return embed_copy(env, vc->newConcatExpr(kids));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVExtractExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr, jint jhi, jint jlow)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    int hi(jhi);
    int low(jlow);
    return embed_copy(env, vc->newBVExtractExpr(*expr, hi, low));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVNegExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->newBVNegExpr(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVAndExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVAndExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVAndExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jkids)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> kids(toCppV<Expr>(env, jkids));
    return embed_copy(env, vc->newBVAndExpr(kids));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVOrExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVOrExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVOrExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jkids)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> kids(toCppV<Expr>(env, jkids));
    return embed_copy(env, vc->newBVOrExpr(kids));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVXorExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVXorExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVXorExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jkids)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> kids(toCppV<Expr>(env, jkids));
    return embed_copy(env, vc->newBVXorExpr(kids));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVXnorExpr1
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVXnorExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVXnorExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jkids)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> kids(toCppV<Expr>(env, jkids));
    return embed_copy(env, vc->newBVXnorExpr(kids));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVNandExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVNandExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVNorExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVNorExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVLTExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVLTExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVLEExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVLEExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVSLTExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVSLTExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVSLEExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVSLEExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewSXExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr, jint jlen)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    int len(jlen);
    return embed_copy(env, vc->newSXExpr(*expr, len));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVUminusExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->newBVUminusExpr(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVSubExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVSubExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVPlusExpr
(JNIEnv* env, jclass, jobject jvc, jint jnumbits, jobjectArray jexprs)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    int numbits(jnumbits);
    vector<Expr> exprs(toCppV<Expr>(env, jexprs));
    return embed_copy(env, vc->newBVPlusExpr(numbits, exprs));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVMultExpr
(JNIEnv* env, jclass, jobject jvc, jint jnumbits, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    int numbits(jnumbits);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVMultExpr(numbits, *expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVUDivExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVUDivExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVURemExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVURemExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVSDivExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVSDivExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVSRemExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVSRemExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewBVSModExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr1, jobject jexpr2)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr1 = unembed_const<Expr>(env, jexpr1);
    const Expr* expr2 = unembed_const<Expr>(env, jexpr2);
    return embed_copy(env, vc->newBVSModExpr(*expr1, *expr2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewFixedLeftShiftExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr, jint jr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    int r(jr);
    return embed_copy(env, vc->newFixedLeftShiftExpr(*expr, r));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewFixedConstWidthLeftShiftExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr, jint jr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    int r(jr);
    return embed_copy(env, vc->newFixedConstWidthLeftShiftExpr(*expr, r));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniNewFixedRightShiftExpr
(JNIEnv* env, jclass, jobject jvc, jobject jexpr, jint jr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    int r(jr);
    return embed_copy(env, vc->newFixedRightShiftExpr(*expr, r));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniTupleExpr
(JNIEnv* env, jclass, jobject jvc, jobjectArray jexprs)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> exprs(toCppV<Expr>(env, jexprs));
    return embed_copy(env, vc->tupleExpr(exprs));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniTupleSelectExpr
(JNIEnv* env, jclass, jobject jvc, jobject jtuple, jint jindex)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* tuple = unembed_const<Expr>(env, jtuple);
    int index(jindex);
    return embed_copy(env, vc->tupleSelectExpr(*tuple, index));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniTupleUpdateExpr
(JNIEnv* env, jclass, jobject jvc, jobject jtuple, jint jindex, jobject jvalue)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* tuple = unembed_const<Expr>(env, jtuple);
    int index(jindex);
    const Expr* value = unembed_const<Expr>(env, jvalue);
    return embed_copy(env, vc->tupleUpdateExpr(*tuple, index, *value));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniDatatypeConsExpr
(JNIEnv* env, jclass, jobject jvc, jstring jconstructor, jobjectArray jexprs)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string constructor(toCpp(env, jconstructor));
    vector<Expr> exprs(toCppV<Expr>(env, jexprs));
    return embed_copy(env, vc->datatypeConsExpr(constructor, exprs));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniDatatypeSelExpr
(JNIEnv* env, jclass, jobject jvc, jstring jselector, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string selector(toCpp(env, jselector));
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->datatypeSelExpr(selector, *expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniDatatypeTestExpr
(JNIEnv* env, jclass, jobject jvc, jstring jconstructor, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string constructor(toCpp(env, jconstructor));
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->datatypeTestExpr(constructor, *expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniForallExpr1
(JNIEnv* env, jclass, jobject jvc, jobjectArray jvars, jobject jbody)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> vars(toCppV<Expr>(env, jvars));
    const Expr* body = unembed_const<Expr>(env, jbody);
    return embed_copy(env, vc->forallExpr(vars, *body));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniForallExpr2
(JNIEnv* env, jclass, jobject jvc, jobjectArray jvars, jobject jbody, jobjectArray jtriggers)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> vars(toCppV<Expr>(env, jvars));
    const Expr* body = unembed_const<Expr>(env, jbody);
    vector<Expr> triggers(toCppV<Expr>(env, jtriggers));
    return embed_copy(env, vc->forallExpr(vars, *body, triggers));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniSetTriggers
(JNIEnv* env, jclass, jobject jvc, jobject jclosure, jobjectArray jtriggers)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* closure = unembed_const<Expr>(env, jclosure);
    vector<Expr> triggers(toCppV<Expr>(env, jtriggers));
    vc->setTriggers(*closure, triggers);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniExistsExpr
(JNIEnv* env, jclass, jobject jvc, jobjectArray jvars, jobject jbody)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> vars(toCppV<Expr>(env, jvars));
    const Expr* body = unembed_const<Expr>(env, jbody);
    return embed_copy(env, vc->existsExpr(vars, *body));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniLambdaExpr
(JNIEnv* env, jclass, jobject jvc, jobjectArray jvars, jobject jbody)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> vars(toCppV<Expr>(env, jvars));
    const Expr* body = unembed_const<Expr>(env, jbody);
    return embed_copy(env, vc->lambdaExpr(vars, *body));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniTransClosure
(JNIEnv* env, jclass, jobject jvc, jobject jp)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Op* p = unembed_const<Op>(env, jp);
    return embed_copy(env, vc->transClosure(*p));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniSimulateExpr
(JNIEnv* env, jclass, jobject jvc, jobject jf, jobject js, jobjectArray jinputs, jobject jn)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* f = unembed_const<Expr>(env, jf);
    const Expr* s = unembed_const<Expr>(env, js);
    vector<Expr> inputs(toCppV<Expr>(env, jinputs));
    const Expr* n = unembed_const<Expr>(env, jn);
    return embed_copy(env, vc->simulateExpr(*f, *s, inputs, *n));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniSetResourceLimit
(JNIEnv* env, jclass, jobject jvc, jint jlimit)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    int limit(jlimit);
    vc->setResourceLimit(limit);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniAssertFormula
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    vc->assertFormula(*expr);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniRegisterAtom
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    vc->registerAtom(*expr);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetImpliedLiteral
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->getImpliedLiteral());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniSimplify
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return embed_copy(env, vc->simplify(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_ValidityChecker_jniQuery
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJava(env, vc->query(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_ValidityChecker_jniCheckUnsat
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJava(env, vc->checkUnsat(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_ValidityChecker_jniCheckContinue
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return toJava(env, vc->checkContinue());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_ValidityChecker_jniRestart
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJava(env, vc->restart(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniReturnFromCheck
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vc->returnFromCheck();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniGetUserAssumptions
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> result;
    vc->getUserAssumptions(result);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniGetInternalAssumptions
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> result;
    vc->getInternalAssumptions(result);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniGetAssumptions
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> result;
    vc->getAssumptions(result);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniGetAssumptionsUsed
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> result;
    vc->getAssumptionsUsed(result);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniGetCounterExample
(JNIEnv* env, jclass, jobject jvc, jboolean jinOrder)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    bool inOrder(jinOrder);
    vector<Expr> result;
    vc->getCounterExample(result, inOrder);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniGetConcreteModel
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    ExprMap<Expr> result;
    vc->getConcreteModel(result);
    return toJavaHCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_ValidityChecker_jniGetValue
(JNIEnv* env, jclass, jobject jvc, jobject jexpr)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    const Expr* expr = unembed_const<Expr>(env, jexpr);
    return toJava(env, vc->value(*expr));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_ValidityChecker_jniInconsistent1
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return vc->inconsistent();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniInconsistent2
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> result;
    bool inconsistent = vc->inconsistent(result);
    assert(inconsistent);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_ValidityChecker_jniIncomplete1
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return vc->incomplete();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniIncomplete2
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<std::string> result;
    bool incomplete = vc->incomplete(result);
    assert(incomplete);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetProof
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->getProof());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetTCC
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->getTCC());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_ValidityChecker_jniGetAssumptionsTCC
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vector<Expr> result;
    vc->getAssumptionsTCC(result);
    return toJavaVCopy(env, result);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetProofTCC
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->getProofTCC());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetClosure
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->getClosure());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetProofClosure
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_copy(env, vc->getProofClosure());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_ValidityChecker_jniStackLevel
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return vc->stackLevel();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniPush
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vc->push();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniPop
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vc->pop();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniPopTo
(JNIEnv* env, jclass, jobject jvc, jint jstackLevel)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    int stackLevel(jstackLevel);
    vc->popto(stackLevel);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_ValidityChecker_jniScopeLevel
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return vc->scopeLevel();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniPushScope
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vc->pushScope();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniPopScope
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vc->popScope();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniPopToScope
(JNIEnv* env, jclass, jobject jvc, jint jstackLevel)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    int stackLevel(jstackLevel);
    vc->poptoScope(stackLevel);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetCurrentContext
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_mut_ref(env, vc->getCurrentContext());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniLoadFile1
(JNIEnv* env, jclass, jobject jvc, jstring jfileName, jstring jlang)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    string fileName(toCpp(env, jfileName));
    string lang(toCpp(env, jlang));
    vc->loadFile(fileName, toCppInputLanguage(env, lang), false);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_ValidityChecker_jniGetStatistics
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    return embed_mut_ref(env, &vc->getStatistics());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniPrintStatistics
(JNIEnv* env, jclass, jobject jvc)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    vc->printStatistics();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_ValidityChecker_jniSetTimeLimit
(JNIEnv* env, jclass, jobject jvc, jint jn)
{
  try {
    ValidityChecker* vc = unembed_mut<ValidityChecker>(env, jvc);
    int n(jn);
    vc->setTimeLimit((uint)n);
  } catch (const Exception& e) { toJava(env, e); };
}

