#ifndef YYSTYPE_H
#define YYSTYPE_H

#define YYSTYPE ast_node*

#include <cstdio>
#include <string>
#include <list>
#include <fstream>

using namespace std;

extern bool verbose_mode;
extern int yylineno;
extern void yyerror(const char *s, ...);
extern int yylex(void);
extern void yyrestart(FILE*);
extern void info(const char *s, ...);
 

enum ast_types {
	ast_slc=100,
	ast_SIN,
	ast_FOR,
	ast_loop_init,
	ast_loop_test,
	ast_loop_update,
	ast_IDENTIFIER,
	ast_memref,
	ast_INT,
	ast_FLOAT,
	ast_seq_of_stmts,
	ast_GETS,
	ast_expression,
	ast_UNDEFINED=999999
};

extern const std::string type2string(ast_types t);

class ast_node {
private:
	int id;
	static int id_counter;
	ast_node(): id(-1), type(ast_UNDEFINED), value("") {}
public:
	ast_types type; 
	std::string value;
	std::list<ast_node*> children;
	ast_node(ast_types t, std::string s): id(id_counter++), type(t), value(s) {}
	friend void ast_visitor(const ast_node* const ast, ofstream& ofs);
	friend void ast2python_visitor(const ast_node* const ast, ofstream& ofs);
};

class source {
public:
	std::string filename;
	ast_node* ast;
	int parseresult;
};

#endif
