#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include <iostream>
extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;
static Decl curr_decl = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;
typedef SymbolTable<Symbol, Decl> DeclEnvironment;
DeclEnvironment declEnv;

///////////////////////////////////////////////

// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}
bool flag = false;
bool flag_return = false;
//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol
    Int,
    Float,
    String,
    Bool,
    Void,
    Main,
    print
    ;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic
    analysis in a recursive way.
    Of course, you can add any other funant test/testctions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

static void install_calls(Decls decls) {
    declEnv.enterscope();
    for(int i=decls->first(); decls->more(i); i=decls->next(i)){
        Decl decl = decls->nth(i);
        if(decl->isCallDecl()){
            if(!isValidCallName(decl->getName())){                          //can't be printf
                semant_error(decl)<<"Function printf cannot be redefination.\n";
                semant_error(decl)<<"Function printf cannot have a name as printf.\n";
            }
            else {
                if (declEnv.probe(decl->getName()) != NULL)                     // can't define twice
                    semant_error(decl) << "Function " << decl->getName() << " was previously defined.\n";
                else
                    declEnv.addid(decl->getName(),new Decl(decl));                   //else we can add it into the table
            }
        }
    }
}

static void install_globalVars(Decls decls) {
    objectEnv.enterscope();
    for(int i=decls->first(); decls->more(i); i=decls->next(i)){
        Decl decl = decls->nth(i);
        if(!decl->isCallDecl()){
            if(objectEnv.probe(decl->getName())!=NULL)
                semant_error(decl) << decl->getName() << "has been defined before.\n";
            else{
                if(!isValidTypeName(decl->getType()))
                    semant_error(decl) << "var " << decl->getName() << " cannot be of type Void. Void can just be used as return type.\n";
                else objectEnv.addid(decl->getName(), new Symbol(decl->getType()));
            }
        }
    }
}

static void check_calls(Decls decls) {
    for (int i = decls->first(); decls->more(i); i = decls->next(i)){
        if (decls->nth(i)->isCallDecl())
            decls->nth(i)->check();
    }
}

static void check_main() {
    if(declEnv.probe(Main)==NULL){
        semant_error() << "Function main is needed\n";
    }
    else {
        CallDecl decl = CallDecl(*(declEnv.probe(Main)));
        if (isValidTypeName(decl->getType()))
            semant_error(decl) << "Main function should have return type Void.\n";
        else if (decl->getVariables()->len()!=0)
            semant_error(decl) << "main have no parameters\n";
    }
}

void VariableDecl_class::check() {
    if (objectEnv.lookup(variable->getName()) != NULL) {
        objectEnv.addid(variable->getName(), new Symbol(variable->getType()));
        semant_error(variable) << "var " << variable->getName() << "can't bedefined twice\n";
    }
    else {
        if (!isValidTypeName(variable->getType()))
            semant_error(variable) << "var " << variable->getName() << " cannot be of type Void. Void can just be used as return type.\n";
        else
            objectEnv.addid(variable->getName(), new Symbol(variable->getType()));
    }
}

void CallDecl_class::check() {
    flag_return=true;
    objectEnv.enterscope();                         //this function is to check a function declaration
    if(returnType != Void && returnType != Int && returnType != Float && returnType != Bool && returnType != String)
        semant_error() << "return type error\n";
    for (int i = paras->first(); paras->more(i); i = paras->next(i)) {
        Variable parameter = paras->nth(i);
        if(objectEnv.probe(parameter->getName())!=NULL)
            semant_error(parameter) << parameter->getName() << "there is a duplicate name\n";
        else {
            if(!isValidTypeName(parameter->getType()))
                semant_error(parameter) << "Function " << name << " 's parameter has an invalid type Void.\n";
            else
                objectEnv.addid(parameter->getName(), new Symbol(parameter->getType()));
        }
    }
    this->getBody()->check(this->getType());
    if(flag_return)
        semant_error(this) << "Function " << name << " must have an overall return statement.\n";
    objectEnv.exitscope();
}

void StmtBlock_class::check(Symbol type) {
    for(int i = vars->first(); vars->more(i); i=vars->next(i)){
        vars->nth(i)->check();
    }
    for(int i = stmts->first(); stmts->more(i); i = stmts->next(i)){
        objectEnv.enterscope();
        stmts->nth(i)->check(type);
        objectEnv.exitscope();
    }
}

void IfStmt_class::check(Symbol type) {
    Symbol condition_type = condition->checkType();
    if(!sameType(condition_type, Bool))
        semant_error(this) << "Condition must be a bool, got " << condition_type << ".\n";
    thenexpr->check(type);
    elseexpr->check(type);
}

void WhileStmt_class::check(Symbol type) {
    Symbol condition_type = condition->checkType();
    if(!sameType(condition_type, Bool))
        semant_error(condition) << "Condition must be a bool, got " << condition_type << ".\n";
    flag=true;
    body->check(type);
    flag=false;
}

void ForStmt_class::check(Symbol type) {
    flag=true;
    if(!condition->is_empty_Expr()&&(!sameType(condition->checkType(), Bool)))
        semant_error(condition) << "Condition must be a bool, got " << condition->getType() << ".\n";
    initexpr->check(type);
    loopact->check(type);
    body->check(type);
    flag=false;
}

void ReturnStmt_class::check(Symbol type) {
    flag_return = false;
    Symbol valueType = value->checkType();
    if(!sameType(valueType, type))
        semant_error(value) << "Returns " << valueType <<" , but need " << type << '\n';
}

void ContinueStmt_class::check(Symbol type) {
    if(!flag)
        semant_error(this) << "continue must be used in a loop sentence.\n";
}

void BreakStmt_class::check(Symbol type) {
    if(!flag)
        semant_error(this) << "break must be used in a loop sentence.\n";
}

Symbol Call_class::checkType(){                 //call a function
    if(!isValidTypeName(name)){                             //if the function is printf
        if(actuals->len()==0)
            semant_error(this) << "function printf should have at least one parameter\n";
        else {
            if(!sameType(actuals->nth(actuals->first())->checkType(), String))
                semant_error(this) << "the first parameter of printf must be String\n";
            else{
                for(int i=actuals->first(); actuals->more(i); i=actuals->next(i)) {
                    actuals->nth(i)->checkType();
                    if(!isValidTypeName(actuals->nth(i)->getType()))
                        semant_error(this) << "the type of actuals can't be void\n";
                }
            }
        }
        setType(Void);
        return type;
    }
    else {
        if(declEnv.lookup(name)==NULL) {
            semant_error(this) << "Function " << name << " has not been defined\n";
            setType(Void);
            return type;
        }
        else {
            CallDecl decl_call = CallDecl(*(declEnv.probe(name)));
            Variables decl_paras = decl_call->getVariables();
            Symbol decl_type = decl_call->getType();
            int i = actuals->first();
            int j = decl_paras->first();
            while ((actuals->more(i) == true)&& (decl_paras->more(j) == true)){
                if(!sameType(decl_paras->nth(j)->getType() ,actuals->nth(i)->checkType())){
                    semant_error(this)<<"Function "<<name<<", the "<<i + 1<<" parameter should be "<<decl_paras->nth(j)->getType()<<" but provided a " << actuals->nth(i)->getType() << endl;
                    break;
                }
                i = actuals->next(i);
                j = decl_paras->next(j);
            }
            if ((decl_paras->more(i) && !actuals->more(j)) || (!decl_paras->more(i) && actuals->more(j))) {
                semant_error(this) << i << " parameters needed, but " << j << "parameters provided\n";
            }
            setType(decl_type);
            return type;
        }
    }
}

Symbol Actual_class::checkType(){
    setType(expr->checkType());
    return type;
}

Symbol Assign_class::checkType(){
    if(objectEnv.lookup(lvalue)!=NULL){
        setType(*objectEnv.lookup(lvalue));
    }
    else {
            semant_error(this) << "left value " << lvalue << " has not been defined\n";
            setType(Void);
    }
    Symbol value_type = value->checkType();
    if(!sameType(value_type, type)){
        semant_error(this) << "Right value must have type " << type << " , got " << value_type << ".\n";
    }
    return type;
}

Symbol Add_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Int)&&sameType(type2, Int)){
        setType(Int);
    }
    else if((sameType(type1, Int)&&sameType(type2, Float))||(sameType(type1, Float)&&sameType(type2, Int))||(sameType(type1, Float)&&sameType(type2, Float))){
        setType(Float);
    }
    else {
        semant_error(this) << "the value type in add must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Minus_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Int)&&sameType(type2, Int)){
        setType(Int);
    }
    else if((sameType(type1, Int)&&sameType(type2, Float))||(sameType(type1, Float)&&sameType(type2, Int))||(sameType(type1, Float)&&sameType(type2, Float))){
        setType(Float);
    }
    else {
        semant_error(this) << "the value type in add must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Multi_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Int)&&sameType(type2, Int)){
        setType(Int);
    }
    else if((sameType(type1, Int)&&sameType(type2, Float))||(sameType(type1, Float)&&sameType(type2, Int))||(sameType(type1, Float)&&sameType(type2, Float))){
        setType(Float);
    }
    else {
        semant_error(this) << "the value type in add must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Divide_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Int)&&sameType(type2, Int)){
        setType(Int);
    }
    else if((sameType(type1, Int)&&sameType(type2, Float))||(sameType(type1, Float)&&sameType(type2, Int))||(sameType(type1, Float)&&sameType(type2, Float))){
        setType(Float);
    }
    else {
        semant_error(this) << "the value type in add must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Mod_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Int)&&sameType(type2, Int)){
        setType(Int);
    }
    else {
        semant_error(this) << "the value in the mod must be Int\n";
        setType(Void);
    }
    return type;
}

Symbol Neg_class::checkType(){
    Symbol value_type = e1->checkType();
    if(sameType(value_type, Int)||sameType(value_type, Float)){
        setType(value_type);
    }
    else {
        semant_error(this) << "the value in the negative must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Lt_class::checkType(){
     Symbol type1 = e1->checkType();
     Symbol type2 = e2->checkType();
     if((sameType(type1, Int)||sameType(type1, Float))&&(sameType(type2, Int)||sameType(type1, Float))){
         setType(Bool);
     }
     else {
         semant_error(this) << "value type in the less comparision must be Int or Float\n";
         setType(Void);
     }
     return type;
}

Symbol Le_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if((sameType(type1, Int)||sameType(type1, Float))&&(sameType(type2, Int)||sameType(type1, Float))){
        setType(Bool);
    }
    else {
        semant_error(this) << "value type in the lessEaual comparision must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Equ_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if((sameType(type1, Int)||sameType(type1, Float)||sameType(type1, Bool))&&(sameType(type2, Int)||sameType(type1, Float)||sameType(type2, Bool))){
        setType(Bool);
    }
    else {
        semant_error(this) << "value type in the equal comparision must be Int or Float or Bool\n";
        setType(Void);
    }
    return type;
}

Symbol Neq_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if((sameType(type1, Int)||sameType(type1, Float)||sameType(type1, Bool))&&(sameType(type2, Int)||sameType(type1, Float)||sameType(type2, Bool))){
        setType(Bool);
    }
    else {
        semant_error(this) << "value type in the not equal comparision must be Int or Float or Bool\n";
        setType(Void);
    }
    return type;
}

Symbol Ge_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if((sameType(type1, Int)||sameType(type1, Float))&&(sameType(type2, Int)||sameType(type1, Float))){
        setType(Bool);
    }
    else {
        semant_error(this) << "value type in the greater or equal comparision must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Gt_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if((sameType(type1, Int)||sameType(type1, Float))&&(sameType(type2, Int)||sameType(type1, Float))){
        setType(Bool);
    }
    else {
        semant_error(this) << "value type in the greater comparision must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol And_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Bool)&&sameType(type2, Bool)){
        setType(Bool);
    }
    else {
        semant_error(this) << "value type in the and must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Or_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Bool)&&sameType(type2, Bool)){
        setType(Bool);
    }
    else {
        semant_error(this) << "value type in the or must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Xor_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Bool)&&sameType(type2, Bool)){
        setType(Bool);
    }
    else if(sameType(type1, Int)&&sameType(type2, Int)){
        setType(Int);
    }
    else {
        semant_error(this) << "value type in the exclusive-or must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Not_class::checkType(){
    Symbol type1 = e1->checkType();
    if(sameType(type1, Bool)){
        setType(Bool);
    }
    else {
        semant_error(this) << "value type in the not must be Int or Float\n";
        setType(Void);
    }
    return type;
}

Symbol Bitand_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Int)&&sameType(type2, Int)){
        setType(Int);
    }
    else {
        semant_error(this) << "the variable type in bitand must be Int\n";
        setType(Void);
    }
    return type;
}

Symbol Bitor_class::checkType(){
    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();
    if(sameType(type1, Int)&&sameType(type2, Int)){
        setType(Int);
    }
    else {
        semant_error(this) << "the variable type in bitor must be Int\n";
        setType(Void);
    }
    return type;
}

Symbol Bitnot_class::checkType(){
    Symbol type1 = e1->checkType();
    if(sameType(type1, Int)){
        setType(Int);
    }
    else {
        semant_error(this) << "the variable type in bitnot must be Int\n";
        setType(Void);
    }
    return type;
}

Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

Symbol Object_class::checkType(){
    if(objectEnv.lookup(var)!=NULL){
        setType(*objectEnv.lookup(var));
    }
    else {
        semant_error(this) << "object " << var << " has not been defined\n";
        setType(Void);
    }
    return type;
}

Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

void Program_class::semant() {
    initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



