
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

#include <iostream>
#include <sstream>
#include <cstdlib>
#include <string>
#include <vector>

using namespace std;

#include "common-classes.hh"
#include "evaluate.hh"
#include "reg-alloc.hh"
#include "symtab.hh"
#include "ast.hh"
#include "options.hh"
#include "support.hh"
#include "icode.hh"

/* 
    Please see the documentation in file ast.hh for a description of the
    classes. Here we provide an implementation of the class methods.
*/

/************* Methods for class asgn_Ast ******************/
void asgn_Ast::print_Node(ostream * asgn_fp)
{
    if(!(left->get_Sym_Entry())->exp_var_flag) {
        *asgn_fp << " Asgn: (LHS (";
        left->print_Node(asgn_fp);
        *asgn_fp << "), RHS (";
        right->print_Node(asgn_fp);
        *asgn_fp << "))\n";
    }
}

/************* Methods for class ret_Ast ******************/
void ret_Ast::print_Node(ostream * ret_fp) 
{ 
    *ret_fp << " Return\n";
}

/************* Methods for class name_Ast ******************/
void name_Ast::print_Node(ostream * name_fp)
{
    *name_fp << "Name:(" << name << ")";
}

/************* Methods for class float_Ast ******************/
void float_Ast::print_Node(ostream * num_fp)
{
    num_fp->setf(std::ios::fixed);
    num_fp->precision(6);
    *num_fp << "Num:(" << fum << ")";
}

/************* Methods for class num_Ast ******************/
void int_Ast::print_Node(ostream * num_fp)
{
    *num_fp << "Num:(" << num << ")";
}

/************* Methods for class geq_Ast ******************/
void geq_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "GE: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}

/************* Methods for class leq_Ast ******************/
void leq_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "LE: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}

/************* Methods for class gt_Ast ******************/
void gt_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "GT: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}

/************* Methods for class lt_Ast ******************/
void lt_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "LT: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}

/************* Methods for class eq_Ast ******************/
void eq_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "EQ: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}

/************* Methods for class meq_Ast ******************/
void neq_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "NE: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}

/************* Methods for class plus_Ast ******************/
void plus_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "PLUS: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}


/************* Methods for class minus_Ast ******************/
void minus_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "MINUS: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}


/************* Methods for class unary_minus_Ast ******************/
void unary_minus_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "UMINUS: ((";
    ft->print_Node(asgn_fp);
    *asgn_fp << "))";
}


/************* Methods for class mult_Ast ******************/
void mult_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "MULT: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}


/************* Methods for class div_Ast ******************/
void div_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << "DIV: ((";
    left->print_Node(asgn_fp);
    *asgn_fp << "), (";
    right->print_Node(asgn_fp);
    *asgn_fp << "))";
}


/************* Methods for class goto_Ast ******************/
void goto_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << " Goto: ( bb_"<<get_Int()<<")\n";
}


/************* Methods for class if_Ast ******************/
void if_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << " If_goto: ((";
    ft->print_Node(asgn_fp);
    *asgn_fp << "), bb_"<<left->get_Int()<<", bb_"<<right->get_Int()<<")\n";
}


/************* Methods for evaluating result ******************/
static ostream * eval_fp = NULL;

void asgn_Ast::print_Eval_Result(asgn_Ast * ast)
{
    if(!(left->get_Sym_Entry())->exp_var_flag) {
        eval_fp = cmd_options.output_File();
        *eval_fp << " Statement ";
        ast->print_Node(eval_fp);
        *eval_fp << " After evaluation ";
        sym_Entry_Ptr se_P = ast->left->get_Sym_Entry();
        se_P->print_Sym_Entry_Eval_Details(eval_fp);
    }
}

void goto_Ast::print_Eval_Result(goto_Ast * ast)
{
    eval_fp = cmd_options.output_File();
    *eval_fp << " Statement ";
    ast->print_Node(eval_fp);
    *eval_fp << " Jumping to basic block "<<num<<"\n";
}

void if_Ast::print_Eval_Result(if_Ast * ast)
{
    eval_fp = cmd_options.output_File();
    *eval_fp << " Statement ";
    ast->print_Node(eval_fp);
    eval_Result i_res = ft->evaluate();
    if(i_res.get_Int_Val() == 0) {
        *eval_fp << " The condition is False ";
        *eval_fp << " Jumping to basic block "<<right->get_Int()<<"\n";
    } else {
        *eval_fp << " The condition is True ";
        *eval_fp << " Jumping to basic block "<<left->get_Int()<<"\n";
    }
}
