 /*
  *  The scanner definition for seal.
  */

 /*
  *  Stuff enclosed in %{ %} in the first section is copied verbatim to the
  *  output, so headers and global definitions are placed here to be visible
  * to the code in the file.  Don't remove anything that was here initially
  */
%{
#include <string>
#include <stdio.h>
#include <seal-parse.h>
#include <stringtab.h>
#include <utilities.h>
#include <stdint.h>
#include <stdlib.h>
#include <string>
/* The compiler assumes these identifiers. */
#define yylval seal_yylval
#define yylex  seal_yylex

/* Max size of string constants */
#define MAX_STR_CONST 256
#define YY_NO_UNPUT   /* keep g++ happy */
#

extern FILE *fin; /* we read from this file */

/* define YY_INPUT so we read from the FILE fin:
 * This change makes it possible to use this scanner in
 * the seal compiler.
 */
#undef YY_INPUT
#define YY_INPUT(buf,result,max_size) \
	if ( (result = fread( (char*)buf, sizeof(char), max_size, fin)) < 0) \
		YY_FATAL_ERROR( "read() in flex scanner failed");

char string_buf[MAX_STR_CONST]; /* to assemble string constants */
char *string_buf_ptr;

static std::string cur_string;
static int count=0;   // check whether /* and */ matched or not
static bool flag=false;

extern int curr_lineno;
extern int verbose_flag;

extern YYSTYPE seal_yylval;

/*
 *  Add Your own definitions here
 */


%}
%option noyywrap
 /*
  * Define names for regular expressions here.
  */
DIGIT [0-9]
LOWERCASE [a-z]
HIGHERCASE [A-Z]
HEXDIGIT [0-9a-fA-F]
%x COMMENTS STRING1 STRING2

%%

 /*
 *	Add Rules here. Error function has been given.
 */

 //MATCH COMMENTS
<INITIAL,COMMENTS>"/*" {
    count++;
    BEGIN(COMMENTS);
}
<COMMENTS>"*/" {
    --count;
    if(count==0)
        BEGIN(0);
}
<COMMENTS>"\n" {++curr_lineno;}
<COMMENTS>[^"\n""*/""/*"] {}
<COMMENTS><<EOF>> {
    strcpy(seal_yylval.error_msg, "EOF in comment");
    BEGIN 0;
    return (ERROR);
}
"*/" {strcpy(seal_yylval.error_msg, "not matched */"); return ERROR;}



 /*string start with "*/
<INITIAL>"\"" {
    cur_string = "";
    flag = false;
    BEGIN(STRING1);
}
<STRING1>"\\" {
    char c = yyinput();
    switch(c) {
        case 'b': cur_string+='\b';break;
        case 't': cur_string+='\t';break;
        case '0': strcpy(seal_yylval.error_msg, "String contains null character '\\0'"); flag = true;return ERROR;
        case 'n': cur_string+='\n';break;
        default: cur_string+=c;
    }
}
<STRING1>"\"" {
    if(cur_string.size() > MAX_STR_CONST){
        strcpy(seal_yylval.error_msg, "String is too long");
        BEGIN(0);
        return ERROR;
    }
    BEGIN(0);
    if(!flag){
        seal_yylval.symbol = stringtable.add_string((char *) cur_string.c_str());
        flag = false;
        return CONST_STRING;
    }
}
<STRING1>. {
    cur_string+=yytext;
}
<STRING1>"\\\n" {
    ++curr_lineno;
    cur_string += "\n";
}
<STRING1>"\n" {
    strcpy(seal_yylval.error_msg, "newline in quotation must use a '\\'");
    BEGIN(0);
    ++curr_lineno;
    return ERROR;
}
<STRING1><<EOF>> {
    strcpy(seal_yylval.error_msg, "EOF in string constant");
    flag = true;
    return ERROR;
}


 /*string start with ` */
<INITIAL>"`" {
    cur_string = "";
    BEGIN(STRING2);
}
<STRING2>"\n" {
    ++curr_lineno;
    cur_string += "\n";
}
<STRING2>"`" {
    if(cur_string.size() > MAX_STR_CONST){
        strcpy(seal_yylval.error_msg, "String is too long");
        BEGIN(0);
        return ERROR;
    }
    BEGIN(0);
    if(!flag){
        seal_yylval.symbol = stringtable.add_string((char *) cur_string.c_str());
        flag = false;
        return CONST_STRING;
    }
}
<STRING2>. {cur_string += yytext;}
<STRING2><<EOF>> {
    strcpy(seal_yylval.error_msg, "EOF in string constant");
    flag = true;
    return ERROR;
}

0[xX][0-9a-zA-Z]+ {
    long long n=0;
    for(int i=2;i<yyleng;++i){
        if(isdigit(yytext[i])){
            n=yytext[i]-'0'+n*16;
        }
        else n=tolower(yytext[i])-'a'+10+n*16;
    }
    std::string s = std::to_string(n);
    seal_yylval.symbol = inttable.add_string((char *)s.c_str());
    return CONST_INT;
}


 /*integers */
{DIGIT}+ {
    seal_yylval.symbol = inttable.add_string(yytext);
    return CONST_INT;
}

{DIGIT}+.{DIGIT}+ {
    seal_yylval.symbol = floattable.add_string(yytext);
    return CONST_FLOAT;
}

 /*bool */
(?i:true) {seal_yylval.boolean = 1;return CONST_BOOL;}
(?i:false) {seal_yylval.boolean = 0;return CONST_BOOL;}

(?i:var)   {return VAR;}
(?i:if) {return IF;}
(?i:else) {return ELSE;}
(?i:while) {return WHILE;}
(?i:for) {return FOR;}
(?i:return) {return RETURN;}
(?i:continue) {return CONTINUE;}
(?i:break) {return BREAK;}
(?i:func) {return FUNC;}
(?i:struct) {return STRUCT;}
(?i:and) {return AND;}

[a-z][0-9a-zA-Z_]* {seal_yylval.symbol = idtable.add_string(yytext);return OBJECTID;}



 /*typeid  */
"Int" {seal_yylval.symbol = idtable.add_string(yytext);return TYPEID;}
"Float" {seal_yylval.symbol = idtable.add_string(yytext);return TYPEID;}
"String" {seal_yylval.symbol = idtable.add_string(yytext);return TYPEID;}
"Void" {seal_yylval.symbol = idtable.add_string(yytext);return TYPEID;}
"Bool" {seal_yylval.symbol = idtable.add_string(yytext);return TYPEID;}

 /*symbols   */
<<EOF>> {return 0;}

[' ''\f''\r''\t''\v']+ {}

">=" {return GE;}
"!=" {return NE;}
"<=" {return LE;}
"==" {return EQUAL;}
"&&" {return AND;}
"||" {return OR;}
"\n" {++curr_lineno;}
"+" {return int('+');}
"-" {return int('-');}
"*" {return int('*');}
"/" {return int('/');}
"%" {return int('%');}
"&" {return int('&');}
"|" {return int('|');}
"^" {return int('^');}
"~" {return int('~');}
"=" {return int('=');}
">" {return int('>');}
"!" {return int('!');}
"<" {return int('<');}
"," {return int(',');}
";" {return int(';');}
":" {return int(':');}
"(" {return int('(');}
")" {return int(')');}
"{" {return int('{');}
"}" {return int('}');}

. {
	strcpy(seal_yylval.error_msg, yytext); 
	return (ERROR); 
}

%%
