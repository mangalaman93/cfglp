
/*********************************************************************************************

                                cfglp : A CFG Language Processor
                                --------------------------------

               About:
               Implemented by Uday Khedker (http://www.cse.iitb.ac.in/~uday) for 
               the courses cs302+cs306: Language Processors (theory and lab) at
               IIT Bombay. Release date Jan 6, 2013. Copyrights reserved by Uday
               Khedker. This implemenation has been made available purely for
               academic purposes without any warranty of any kind.

               Please see the README file for some details. A doxygen generated
               documentation can be found at http://www.cse.iitb.ac.in/~uday/cfglp


***********************************************************************************************/


%skeleton "lalr1.cc"
%language "C++"
%defines
%locations
%left '/' '*'
%left '-' '+'

%define parser_class_name "cfglp"

%{
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <list>
#include <map>
#include <cstring>

using namespace std;

#include "common-classes.hh"
#include "evaluate.hh"
#include "support.hh"
#include "cfglp-ctx.hh"

#include "reg-alloc.hh"
#include "symtab.hh"
#include "ast.hh"
#include "icode.hh"
#include "program.hh"

#include "options.hh"

%}

%parse-param { cfglp_ctx &ctx }
%lex-param   { cfglp_ctx &ctx }

%union 
{
    int ival;
    double fval;
    std::string *sval;
    ast_Ptr ast_P;
    ast_List_Ptr ast_L;
    sym_Entry_Ptr sym_P;
    proc_Ptr proc_P;
    program_Ptr prog_P;
    value_Type type;
    bb_List_Ptr bblp;
};

/* declare tokens */
%token <ival> NUM
%token <fval> DECI
%token <sval> BB_ID ID AVAR EXP_VAR
%token INT FLOAT DOUBLE RETURN STATIC IF ELSE GOTO
%token <sval> COND_VAR RELOP

%type <ast_L> exe_Stmt_List
%type <bblp> bb_List
%type <sym_P> decl_Stmt 
%type <ival> bb_Decl
%type <proc_P> procedure
%type <prog_P> program
%type <sval> Var
%type <ast_P> Expr
%type <ast_P> Number
%type <ast_P> exe_Stmt
%type <type> Type
%type <ast_P> If_goto

%{
  extern int yylex(yy::cfglp::semantic_type *yylval,
       yy::cfglp::location_type* yylloc,
       cfglp_ctx &ctx);

/* Some auxiliary local functions */

  static program_Ptr build_Program(proc_Ptr proc_P, sym_List_Ptr gsym_lp);
  static proc_Ptr build_Procedure (string name, bb_List_Ptr ast_lp,  
                sym_List_Ptr sym_lp, sym_List_Ptr sym_gp);
  static sym_Entry_Ptr redeclaration_Error(string name);
  static ast_Ptr missing_Declaration_Error(bool lhs_d, string lhs_n, bool rhs_d, string rhs_n, int line);
  static ast_Ptr process_Name(string hs, int line);
  static ast_Ptr process_Asgn_Name_expr(string lhs, ast_Ptr rhs, int line);
  static ast_Ptr process_rel_Ast(ast_Ptr lhs, ast_Ptr rhs, string op, int yylineno);
  static bool isExpVar(string name);
  static int whatTypeRelOp(string op);
  static void addSuccessors(bb_List_Ptr bblp);
  static void redeclare_bb_id(int bbn, bb_List_Ptr bblp, int line);
  extern int yylineno;
  extern bb_Ptr getPtrToId(int id, bb_List_Ptr bb_lp);
  static void remove_Consumed_Exp_Var(ast_List_Ptr alp);
  static void set_Remove_Consumed_Exp_Var(ast_List_Ptr alp);
/* 
   Currently our program structure supports global declarations
   and a single procedure without any return type (we need to 
   check that it is the main procedure). We also do not support
   control flow or function calls and our RHS of assignments are 
   simple variables or number and have type INT.

   The complete grammar that we currently support is:

   program: decl_Stmt_List procedure
    |  procedure 
    ;
   procedure: ID '(' ')' '{' decl_Stmt_List bb_Decl exe_Stmt_List '}'
    ;
   decl_Stmt_List: decl_Stmt decl_Stmt_List
    |  decl_Stmt
    ;
   exe_Stmt_List: exe_Stmt_List exe_Stmt 
    |  exe_Stmt 
    ;
   decl_Stmt: static_kw INT ID ';'
    ;
   static_kw: 
    |  STATIC
    ;
   exe_Stmt : ID '=' ID ';'
    |  ID '=' NUM ';'
    |  RETURN ';' 
    ;
   bb_Decl: '<' ID NUM '>' ':'
    ;

   Observe that with a left recursive grammar declaration processing requires 
   inherited attributes because we need to compare current declarations with
   past declarations. 

   Building AST without type checking does not require such a check. Hence it
   can use synthesized attributes. However, type checking during AST building
   requires inherited attributes.

   Synthesized attributes are supported well by bison using the $ notation.
   Inherited attributes limited to a grammar rules can be implemented by
   using $i where i is the position of a grammar symbol in RHS but on the 
   left of current symbol.

   Since bison does not support L-attributed definitions, we do not have a 
   direct mechanism of implementing inherited attributes across grammar 
   rules. Hence we store sym_list in symtab_in_current_scope_P extract it 
   wherever required.

*/
%}

%initial-action {
 // Filename for locations here
 @$.begin.filename = @$.end.filename = new std::string("stdin");
}
%%

start: 
    {
        symtab_in_scope_P = new symtab_In_Scope;
        symtab_in_scope_P->allocate_Sym_List();
    }
    program[prg]
    {
        program_object_P = $prg;
        symtab_in_scope_P->deallocate_Sym_List();
    }
 ;

program: 
    decl_Stmt_List procedure[proc]
    {
        sym_List_Ptr sym_lp = symtab_in_scope_P->get_Symtab_Top_List(); 


        bb_List_Ptr bls = $proc->get_BB_List();
        list<bb_Ptr>::iterator j;
        for(j=bls->begin(); j!=bls->end(); j++) {
            ast_List_Ptr alp = (*j)->get_Ast_List();
            remove_Consumed_Exp_Var(alp);
        }
        
        $$=build_Program($proc, sym_lp);

    }
 |  procedure[proc] 
    {
        bb_List_Ptr bls = $proc->get_BB_List();
        list<bb_Ptr>::iterator j;
        for(j=bls->begin(); j!=bls->end(); j++) {
            ast_List_Ptr alp = (*j)->get_Ast_List();
            remove_Consumed_Exp_Var(alp);
        }
        $$=build_Program($proc, symtab_in_scope_P->get_Symtab_Top_List());
    }
 ;

procedure: 
    ID[id] 
    {
        string name = *$id;

        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false)
            symtab_in_scope_P->enter_Procedure_Name(name, yylineno);
        else
            redeclaration_Error(name);
        symtab_in_scope_P->allocate_Sym_List();
    } 
    '(' ')' '{' decl_Stmt_List bb_List[bblp] '}'
    {
        string name = *$id;
        sym_List_Ptr sym_lp = symtab_in_scope_P->get_Symtab_Local_List(); 
        sym_List_Ptr sym_gp = symtab_in_scope_P->get_Symtab_Global_List();
        addSuccessors($bblp);
        $$ = build_Procedure (name, $bblp, sym_lp, sym_gp);
        symtab_in_scope_P->deallocate_Sym_List();
    }
 ;

bb_List:
    bb_List[blist] bb_Decl[bbn]
    {
        $<ival>$ = yylineno;
    }
    exe_Stmt_List[slist]
    {
        bb_Ptr bbp;
        if ($blist && $slist)
        {
            redeclare_bb_id($bbn, $blist, $<ival>3);
            set_Remove_Consumed_Exp_Var($slist);
            bb_Ptr bbp = new basic_Block($bbn, $slist, $<ival>3);
            $blist->push_back(bbp);
            $$ = $blist;
        }
        else if ($blist && !$slist)
        {
            $$ = $blist;
        }
        else if (!$blist && $slist)
        {
            bb_List_Ptr bblp = new list<bb_Ptr>;
            set_Remove_Consumed_Exp_Var($slist);
            bb_Ptr bbp = new basic_Block($bbn, $slist, $<ival>3);
            bblp->push_back(bbp);
            $$ = bblp;
        }
        else $$ = NULL;
    }
  |
    bb_Decl[bbn]
    {
        $<ival>$ = yylineno;
    }
    exe_Stmt_List[slist]
    {
        bb_List_Ptr bblp;
        bb_Ptr bbp;
        if ($slist)
        { 
            bblp = new list<bb_Ptr>;
            set_Remove_Consumed_Exp_Var($slist);
            bb_Ptr bbp = new basic_Block($bbn, $slist, $<ival>2);
            
            bblp->push_back(bbp);
            $$ = bblp;
        }
        else $$ = NULL;
    }
  ;

exe_Stmt_List:   
    exe_Stmt_List[list] exe_Stmt[item] 
    {
        if ($list && $item)
        {
            ast_List_Ptr ast_lp = $list;
            ast_lp->push_back($item);
            $$ = ast_lp;
        }
        else if ($list && !$item)
        {
            $$ = $list;
        }
        else if (!$list && $item)
        {   
            ast_List_Ptr ast_lp = new list<ast_Ptr>;
            ast_lp->push_back($item);    
            $$ = ast_lp;
        }
        else $$ = NULL;
    }
                
 |  exe_Stmt[stmt]
    {
        if ($stmt)
        { 
            ast_List_Ptr ast_lp = new list<ast_Ptr>;
            ast_lp->push_back($stmt);    
            $$ = ast_lp;
        }
        else $$ = NULL;
    }
 ;

decl_Stmt_List: 
    decl_Stmt_List decl_Stmt[item]
    {
        sym_List_Ptr sym_lp = symtab_in_scope_P->get_Symtab_Top_List(); 
        if ($item)
            sym_lp->insert_Sym_Entry($item);
    }
 |  decl_Stmt[item]
    {
        sym_List_Ptr sym_lp = symtab_in_scope_P->get_Symtab_Top_List(); 
        if ($item)
            sym_lp->insert_Sym_Entry($item);
    }
 ;

decl_Stmt: 
    static_kw Type[type] Var[id] ';'
    {
        string name = *$id;
        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false)
        {
            sym_Entry_Ptr s;
            switch ($type) {
                case int_Val:
                    s = new sym_Entry_for_Int_Var(name, yylineno);
                    s->exp_var_flag = isExpVar(name);
                    $$ = s;
                    break;

                case float_Val:
                    s = new sym_Entry_for_Float_Var(name, yylineno);
                    s->exp_var_flag = isExpVar(name);
                    $$ = s;
                    break;

                default:
                    CHECK_INVARIANT(SHOULD_NOT_REACH, "variblae declaration can only be int or float");
            }
        }
        else
            $$ = redeclaration_Error(name); 
    };

static_kw:  /* empty */
 | STATIC
 ;

bb_Decl: 
    BB_ID[str] ':'
    {
        int i;
        sscanf((*$str).c_str(), "<bb %d>", &i);
        $$ = i;
    }
 ;

exe_Stmt : 
    If_goto[ptr]
    {
        $$ = $ptr;
    }
  |
    GOTO BB_ID[str] ';'
    {
        int i;
        sscanf((*$str).c_str(), "<bb %d>", &i);
        $$ = new goto_Ast(i, yylineno);
    }
  |
	Var[lhs] '=' Expr[rhs] ';'
    {
        $$ = process_Asgn_Name_expr(*$lhs, $rhs, yylineno);
    }
 |  RETURN ';'
 	{
        $$ = new ret_Ast(yylineno);
 	}
 |	Var[lhs] '=' '(' Type[t] ')' '(' Expr[rhs] ')' ';'
	{
        //casting is not enabled
        $$ = process_Asgn_Name_expr(*$lhs, $rhs, yylineno);
	}
 |  Var[lhs] '=' '-' '(' Expr[hs] ')' ';'
    {
        ast_Ptr u_ptr;
        u_ptr = new unary_minus_Ast($hs, yylineno);
        $$ = process_Asgn_Name_expr(*$lhs, u_ptr, yylineno);
    }
 |  Var[lhs] '=' '-' Var[hs] ';'
    {
        ast_Ptr u_ptr, n_ptr;
        n_ptr = process_Name(*$hs, yylineno);
        u_ptr = new unary_minus_Ast(n_ptr, yylineno);
        $$ = process_Asgn_Name_expr(*$lhs, u_ptr, yylineno);
    }
 ;

If_goto:
    IF '(' Var[lhs] RELOP[op] Var[rhs] ')' GOTO BB_ID[if_id] ';' ELSE GOTO BB_ID[else_id] ';'
    {
        int i;
        ast_Ptr l = process_Name(*$lhs, yylineno);
        ast_Ptr r = process_Name(*$rhs, yylineno);
        ast_Ptr cond = process_rel_Ast(l, r, *$op, yylineno);
        sscanf((*$if_id).c_str(), "<bb %d>", &i);
        ast_Ptr if_result = new goto_Ast(i, yylineno);
        sscanf((*$else_id).c_str(), "<bb %d>", &i);
        ast_Ptr else_result = new goto_Ast(i, yylineno);
        $$ = new if_Ast(cond, if_result, else_result, yylineno);
    }
  |
    IF '(' Var[lhs] RELOP[op] Number[num] ')' GOTO BB_ID[if_id] ';' ELSE GOTO BB_ID[else_id] ';'
    {
        int i;
        ast_Ptr l = process_Name(*$lhs, yylineno);
        ast_Ptr cond = process_rel_Ast(l, $num, *$op, yylineno);
        sscanf((*$if_id).c_str(), "<bb %d>", &i);
        ast_Ptr if_result = new goto_Ast(i, yylineno);
        sscanf((*$else_id).c_str(), "<bb %d>", &i);
        ast_Ptr else_result = new goto_Ast(i, yylineno);
        $$ = new if_Ast(cond, if_result, else_result, yylineno);
    }
  |
    IF '(' Number[num1] RELOP[op] Number[num2] ')' GOTO BB_ID[if_id] ';' ELSE GOTO BB_ID[else_id] ';'
    {
        int i;
        ast_Ptr cond = process_rel_Ast($num1, $num2, *$op, yylineno);
        sscanf((*$if_id).c_str(), "<bb %d>", &i);
        ast_Ptr if_result = new goto_Ast(i, yylineno);
        sscanf((*$else_id).c_str(), "<bb %d>", &i);
        ast_Ptr else_result = new goto_Ast(i, yylineno);
        $$ = new if_Ast(cond, if_result, else_result, yylineno);
    }
  ;

Expr:
	Number[hs]
	{
        $$ = $hs;
	}
 |	Var[hs]
 	{
        $$ = process_Name(*$hs, yylineno);
 	}
 |
    '(' Expr[hs] ')'
    {
        $$ = $hs;
    }
 | '(' Type ')' Var[hs]
 	{
        //casting not enabled now
        $$ = process_Name(*$hs, yylineno);
 	}
 |	Expr[lhs] '*' Expr[rhs]
 	{
        ast_Ptr op_ptr = new mult_Ast($lhs, $rhs, yylineno);
        op_ptr->type_Check();
        $$ = op_ptr;
 	}
 |	Expr[lhs] '-' Expr[rhs]
 	{
        ast_Ptr  op_ptr = new minus_Ast($lhs, $rhs, yylineno);
        op_ptr->type_Check();
        $$ = op_ptr;
 	}
 |	Expr[lhs] '+' Expr[rhs]
 	{
        ast_Ptr op_ptr = new plus_Ast($lhs, $rhs, yylineno);
        op_ptr->type_Check();
        $$ = op_ptr;
 	} 
 |	Expr[lhs] '/' Expr[rhs]
 	{
        ast_Ptr op_ptr = new div_Ast($lhs, $rhs, yylineno);
        op_ptr->type_Check();
        $$ = op_ptr;
 	}
 ;

Type:
	INT
	{
		$$ = int_Val;
	}
	| FLOAT
	{
		$$ = float_Val;
	}
  ;

Var:
	ID[hs]
	{
		$$ = $hs;
    }
 |  COND_VAR[hs]
    {
        $$ = $hs;
    }
 |	AVAR[hs]
 	{
 		$$ = $hs;
    }
 |  EXP_VAR[hs]
 	{
        $$ = $hs;
 	}
 ;

Number:
	NUM[hs]
	{
		$$ = new int_Ast($hs, yylineno);
    }
 |	DECI[hs]
 	{
 		$$ = new float_Ast($hs, yylineno);
 	}
 ;

%%

/* Auxiliary functions called in the parser script alone. */
void remove_Consumed_Exp_Var(ast_List_Ptr alp){
  list<ast_Ptr>::iterator i;
  for(i=alp->begin(); i!=alp->end(); i++)
  {
    if((*i)->get_Tree_Op() == asgn)
    {
      ast_Ptr lhs = (*i)->left;
      if(lhs->get_Tree_Op() == name_Leaf)
      {
        sym_Entry_Ptr temp = lhs->get_Sym_Entry();
        if(temp->exp_var_flag)
        {
          if((*i)->delete_flag) {
            i = alp->erase(i);
            i--;
          }
        }
      }
   }
 }
}
void set_Remove_Consumed_Exp_Var(ast_List_Ptr alp){
  list<ast_Ptr>::iterator i;
  for(i=alp->begin(); i!=alp->end(); i++)
  {
    if((*i)->get_Tree_Op() == asgn)
    {
      ast_Ptr lhs = (*i)->left;
      if(lhs->get_Tree_Op() == name_Leaf)
      {
        sym_Entry_Ptr temp = lhs->get_Sym_Entry();
        if(temp->exp_var_flag)
        {
          if(temp->tree_ptr == NULL) {
            (*i)->delete_flag = true;
          }
          else temp->tree_ptr = NULL;
        }
      }
    }
  }
}


program_Ptr build_Program (proc_Ptr proc_P, sym_List_Ptr gsym_lp) 
{
    /*
       We make a pointer to a list of procedure (in this version 
       we have a single procedure).
    */
    proc_Map_Ptr proc_list = new map <string, proc_Ptr>;
    string proc_name = proc_P->get_Name();
    (*proc_list)[proc_name] = proc_P;
    /*
       Now we create a new program object. In this rule of the
       grammar, we have no global declarations.
    */
    program_Ptr prog_P = new program(gsym_lp, proc_list);

    return prog_P;
}

proc_Ptr build_Procedure (string name, bb_List_Ptr bblp,  sym_List_Ptr sym_lp, sym_List_Ptr sym_gp) 
{
     /*
         Then we use the procedure name and declaration list to 
         create a procedure object.
     */ 
    
     proc_Ptr proc_P = new procedure (name, sym_lp, sym_gp, bblp);
     return proc_P;
}

sym_Entry_Ptr redeclaration_Error(string name)
{
    entity_Type en_t = symtab_in_scope_P->get_Entity_Type(name, anywhere);
    value_Type val_t = symtab_in_scope_P->get_Value_Type(name, anywhere);

    string en_s = "";
    string val_s = "";
    en_s = (en_t == entity_Var)? "variable" : "procedure";
    val_s = (val_t == int_Val)? "INT" : "VOID";

    stringstream snum1; 
    snum1 << yylineno;

    string mesg = "Redeclaration of name `" + name + "' in the same scope on line " + snum1.str() + ". ";

    int old_line_no = symtab_in_scope_P->get_Line_Number(name);

    stringstream snum2; 
    snum2 << old_line_no;

    mesg = mesg + "Earlier declaration was as a " + en_s + " of type " + val_s + " on line " + snum2.str() + ". ";
    report_Violation_of_Condition(SHOULD_NOT_REACH, mesg);

    return NULL; 
}

ast_Ptr missing_Declaration_Error(bool lhs_d, string lhs_n, bool rhs_d, string rhs_n, int line)
{
        stringstream sn1; 
        stringstream mesg; 
        sn1 << line;
 
        if ((lhs_d == false) && (rhs_d == false))
                mesg << "Undeclared variables " << lhs_n << "and " << rhs_n << " on line " << line << ".";
        if (lhs_d == false)
        	mesg << "Undeclared variable " << lhs_n << " on line " << line <<  ".";
        else if (rhs_d == false)
        	mesg << "Undeclared variable " << rhs_n << " on line " << line <<  ".";
        else
             CHECK_INVARIANT(SHOULD_NOT_REACH, "Both LHS and RHS variables seem to be declared")
    
        report_Violation_of_Condition (SHOULD_NOT_REACH, mesg.str());
        return NULL; 
}

ast_Ptr process_Asgn_Name_expr(string lhs, ast_Ptr rhs, int line)
{
    ast_Ptr asgn;
    ast_Ptr l;

    bool lhs_d = symtab_in_scope_P->declared_In_Visible_Scope(lhs, anywhere); 

    if (lhs_d)
    {
        l = new name_Ast(lhs, yylineno);
        (l->get_Sym_Entry())->tree_ptr = rhs;
        asgn = new asgn_Ast(l, rhs, line);
//        asgn->type_Check();
    }
    else 
        asgn = missing_Declaration_Error(lhs_d, lhs, true, "dummy_string", line);

    return asgn;
}


ast_Ptr process_Name(string hs, int line)
{ 
    ast_Ptr ptr = NULL;
    sym_Entry_Ptr entry = NULL;
    bool hs_d = symtab_in_scope_P->declared_In_Visible_Scope(hs, anywhere); 

    if (hs_d) {
        if (isExpVar(hs)) {
            entry = (symtab_in_scope_P->get_Symtab_Top_List())->get_Sym_Entry(hs);
            if(entry != NULL) {
                if(entry->tree_ptr != NULL){
                  ptr = entry->tree_ptr;
                  entry->tree_ptr = NULL;
                } else {
                    ptr = new name_Ast(hs, yylineno);
                }
            } else {
                CHECK_INVARIANT(SHOULD_NOT_REACH, "EXP_VAR used before assignment");
            }
        } else {
            ptr = new name_Ast(hs, yylineno);
        }
    } else {
        ptr = missing_Declaration_Error(hs_d, hs, true, "dummy_string", line);
    }

    return ptr;
}

ast_Ptr process_rel_Ast(ast_Ptr lhs, ast_Ptr rhs, string op, int line)
{
    ast_Ptr ptr = NULL;
    switch(whatTypeRelOp(op))
    {
        case 1:
            ptr = new geq_Ast(lhs, rhs, line);
            break;

        case 2:
            ptr = new leq_Ast(lhs, rhs, line);
            break;

        case 3:
            ptr = new gt_Ast(lhs, rhs, line);
            break;

            case 4:
            ptr = new lt_Ast(lhs, rhs, line);
            break;

        case 5:
            ptr = new eq_Ast(lhs, rhs, line);
            break;

        case 6:
            ptr = new neq_Ast(lhs, rhs, line);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "not an expected return from a local function in parse.yy! error occurred!")
            break;
    }

    ptr->type_Check();
    return  ptr;
}

void redeclare_bb_id(int bbn, bb_List_Ptr bblp, int line)
{
    stringstream snum1; 
    snum1 << line;

    stringstream snum3; 
    snum3 << bbn;

    string mesg = "Redeclaration of basic block " + snum3.str() + " on line number " + snum1.str() + ". ";
    list<bb_Ptr>::iterator it;
    for (it = bblp->begin(); it != bblp->end(); it++)
    {
        if((*it)->get_BB_Num() == bbn)
        {
            stringstream snum2;
            snum2 << (*it)->get_Line_Number();
            mesg = mesg + "Earlier declaration was on line " + snum2.str() + ". ";
            report_Violation_of_Condition(SHOULD_NOT_REACH, mesg);
        }
    }
}

bool isExpVar(string name)
{
    int i=0;
    for(i=0; i<name.length(); i++) {
        if (name[i] == '.'){
            name[i] = ' ' ;
            break;
        }
    }
    if(i == name.length()) {return false;}
    int num;
    sscanf(name.c_str(), "%*s %d", &num);
    return (num > 999);
}

int whatTypeRelOp(string op)
{
    if(strcmp(op.c_str(), ">=") == 0) {return 1;}
    else if(strcmp(op.c_str(), "<=") == 0) {return 2;}
    else if(strcmp(op.c_str(), ">") == 0) {return 3;}
    else if(strcmp(op.c_str(), "<") == 0) {return 4;}
    else if(strcmp(op.c_str(), "==") == 0) {return 5;}
    else if(strcmp(op.c_str(), "!=") == 0) {return 6;}
    else {CHECK_INVARIANT(SHOULD_NOT_REACH, "not an expected relational operator! error occurred!") }
}

void addSuccessors(bb_List_Ptr bblp)
{
   bb_Ptr true_S = NULL, false_S = NULL;
   ast_List_Ptr astlp;
   ast_Ptr temp_ap;
   list<bb_Ptr>::iterator i;
   for (i = bblp->begin(); i != bblp->end(); i++)
   {
        true_S = NULL; false_S = NULL;
        astlp = (*i)->get_Ast_List();
        temp_ap = astlp->back();
        if(temp_ap)
        {
           switch(temp_ap->get_Tree_Op())
           {
                case if_node :
                    true_S = getPtrToId(temp_ap->left->get_Int(), bblp);
                    false_S = getPtrToId(temp_ap->right->get_Int(), bblp);
                    break;
                case goto_node :
                    true_S = getPtrToId(temp_ap->get_Int(), bblp);
                    break;
                default:
                    if((++i) != bblp->end()){
                        true_S = (*i);
                    }
                    i--;
                    break;
           }
        }
        (*i)->setSuccessor(true_S, false_S);
    }  
}
