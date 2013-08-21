
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
#include "support.hh"


/* 
    Please see the documentation in file ast.hh for a description of the
    classes. Here we provide an implementation of the class methods.
*/


int ast_Node::get_Int()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Int method cannot be called for a non-num ast node")
}

double ast_Node::get_Float()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Float method cannot be called for a non-num ast node")
}

/************* Methods for class asgn_Ast ******************/

asgn_Ast::asgn_Ast(ast_Ptr  l, ast_Ptr  r, int line)
{
    t_op = asgn;
    node_arity = binary;
    CHECK_INVARIANT(l != NULL, "Left child of an assignment tree node cannot be NULL")
    CHECK_INVARIANT(l->get_Tree_Op() != int_Leaf || l->get_Tree_Op() != float_Leaf, "Left child of an assignment tree node cannot be a number")
    CHECK_INVARIANT(r != NULL, "Right child of an assignment tree node cannot be NULL")
    CHECK_INVARIANT(l->get_Tree_Op() != asgn, "Left child cannot be an assignment node")
    CHECK_INVARIANT(r->get_Tree_Op() != asgn, "Right child cannot be an assignment node")
    left = l;
    right = r;
    lineno = line;
}

asgn_Ast& asgn_Ast::operator=(const asgn_Ast& rhs)
{
    t_op = rhs.t_op;          
    node_arity = rhs.node_arity;
    left = rhs.left;
    right = rhs.right;
    lineno = rhs.lineno;
    return *this;
}

/************* Methods for class ret_Ast ******************/
ret_Ast::ret_Ast(int line) 
{
    t_op = ret;
    lineno = line;
    node_arity = zero_Arity;
}

/************* Methods for class name_Ast ******************/
name_Ast::name_Ast(string n, int line)
{
        t_op = name_Leaf;
        name = n;
        lineno = line;
        node_arity = zero_Arity;
        sym_entry = symtab_in_scope_P->get_Sym_Entry(n);
}

sym_Entry_Ptr name_Ast::get_Sym_Entry()
{
        return sym_entry;
}

/************* Methods for class int_Ast ******************/
int_Ast::int_Ast(int n, int line)
{
    t_op = int_Leaf;
    lineno = line;
    num = n;
    node_arity = zero_Arity;
}

int int_Ast::get_Int()
{
    return num;
}


/************* Methods for class float_Ast ******************/
float_Ast::float_Ast(double f, int line)
{
    t_op = float_Leaf;
    lineno = line;
    fum = f;
    node_arity = zero_Arity;
}

double float_Ast::get_Float()
{
    return fum;
}

/************* Methods for class binary_op_Ast ******************/
binary_op_Ast::binary_op_Ast(ast_Ptr l, ast_Ptr r, int line)
{
    left = l;
    right = r;
    node_arity = binary;
    lineno = line;
}

/************* Methods for class rel_op_Ast ******************/
rel_op_Ast::rel_op_Ast(ast_Ptr l, ast_Ptr r, int line)
    : binary_op_Ast(l, r, line)
{
}

/************* Methods for class geq_Ast ******************/
geq_Ast::geq_Ast(ast_Ptr l, ast_Ptr r, int line)
    : rel_op_Ast(l, r, line)
{
    t_op = geq_node;
}

/************* Methods for class leq_Ast ******************/
leq_Ast::leq_Ast(ast_Ptr l, ast_Ptr r, int line)
    : rel_op_Ast(l, r, line)
{
    t_op = leq_node;
}

/************* Methods for class lt_Ast ******************/
lt_Ast::lt_Ast(ast_Ptr l, ast_Ptr r, int line)
    : rel_op_Ast(l, r, line)
{
    t_op = lt_node;
}

/************* Methods for class gt_Ast ******************/
gt_Ast::gt_Ast(ast_Ptr l, ast_Ptr r, int line)
    : rel_op_Ast(l, r, line)
{
    t_op = gt_node;
}

/************* Methods for class eq_Ast ******************/
eq_Ast::eq_Ast(ast_Ptr l, ast_Ptr r, int line)
    : rel_op_Ast(l, r, line)
{
    t_op = eq_node;
}

/************* Methods for class neq_Ast ******************/
neq_Ast::neq_Ast(ast_Ptr l, ast_Ptr r, int line)
    : rel_op_Ast(l, r, line)
{
    t_op = neq_node;
}

/************* Methods for class mult_Ast ******************/
mult_Ast::mult_Ast(ast_Ptr l, ast_Ptr r, int line)
    : binary_op_Ast(l, r, line)
{
    t_op = mult_node;
}

/************* Methods for class div_Ast ******************/
div_Ast::div_Ast(ast_Ptr l, ast_Ptr r, int line)
    : binary_op_Ast(l, r, line)
{
    t_op = div_node;
}

/************* Methods for class plus_Ast ******************/
plus_Ast::plus_Ast(ast_Ptr l, ast_Ptr r, int line)
    : binary_op_Ast(l, r, line)
{
    t_op = plus_node;
}

/************* Methods for class minus_Ast ******************/
minus_Ast::minus_Ast(ast_Ptr l, ast_Ptr r, int line)
    : binary_op_Ast(l, r, line)
{
    t_op = minus_node;
}

/************* Methods for class unary_op_Ast ******************/
unary_op_Ast::unary_op_Ast(ast_Ptr p, int line)
{
    ft = p;
    node_arity = unary;
    lineno = line;
}

/************* Methods for class unary_minus_Ast ******************/
unary_minus_Ast::unary_minus_Ast(ast_Ptr p, int line)
    : unary_op_Ast(p, line)
{
    t_op = unary_minus_node;
}

/************* Methods for class goto_Ast ******************/
goto_Ast::goto_Ast(int id, int line)
{
    num = id;
    lineno = line;
    t_op = goto_node;
}

int goto_Ast::get_Int()
{
    return num;
}

/************* Methods for class if_Ast ******************/
if_Ast::if_Ast(ast_Ptr cond, ast_Ptr l, ast_Ptr r, int line)
{
    ft = cond;
    left = l;
    right = r;
    t_op = if_node;
    lineno = line;
}
