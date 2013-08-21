
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
#include <ostream>
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
#include "program.hh"
#include "support.hh"
#include "options.hh"

bb_Ptr getPtrToId(int, bb_List_Ptr);

/************* Methods for class ast_Node ******************/
eval_Result ast_Node::get_Value_of_Evaluation()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Value_of_Evaluation cannot be called on a non-name-Ast")
}

void ast_Node::set_Value_of_Evaluation(eval_Result res)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "set_Value_of_Evaluation cannot be called on a non-name-Ast")
}

/************* Methods for class asgn_Ast ******************/
eval_Result asgn_Ast::evaluate()
{
    CHECK_INVARIANT (right != NULL, "Right child of an assignment tree node cannot be NULL")
    eval_Result res = right->evaluate(); 

    CHECK_INVARIANT (left != NULL, "Left child of an assignment tree node cannot be NULL")
    CHECK_INVARIANT (left->get_Tree_Op() == name_Leaf, "LHS of an assignment should be a name")
    left->set_Value_of_Evaluation(res);

    /* 
       Here we really do not need to return the result but since 
       the type of the evaluate function has to remain identical 
       across all derived classes, we return a dummy object which
       has been declared globally.
    */
    print_Eval_Result(this);
    return dummy_result;
}

/************* Methods for class ret_Ast ******************/
eval_Result ret_Ast::evaluate()
{
    /* 
       In this version, we have void procedures only
       hence we return the dummy value which is void.
        
    */
    return dummy_result;
}

/************* Methods for class name_Ast ******************/
eval_Result name_Ast::evaluate()
{
    CHECK_INVARIANT (sym_entry != NULL, "Left child of an assignment tree node cannot be NULL")
    return this->get_Value_of_Evaluation();
}

eval_Result name_Ast::get_Value_of_Evaluation()
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    return sym_entry->get_Value_of_Evaluation();
}

void name_Ast::set_Value_of_Evaluation(eval_Result res)
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    sym_entry->set_Value_of_Evaluation(res);
}

/************* Methods for class mult_Ast ******************/
eval_Result mult_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an multiplication tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an multiplication tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result(Lres.get_Int_Val()*Rres.get_Int_Val(), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result(Lres.get_Float_Val()*Rres.get_Float_Val(), NULL, float_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}

/************* Methods for class div_Ast ******************/
eval_Result div_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an division tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an division tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            CHECK_INVARIANT(Rres.get_Int_Val() != 0,"value of right child of a division tree cannot be 0");
            res = eval_Result(Lres.get_Int_Val()/Rres.get_Int_Val(), NULL, int_Res);
            break;

        case float_Res:
            CHECK_INVARIANT(Rres.get_Float_Val() != 0,"value of right child of a division tree cannot be 0");
            res = eval_Result(Lres.get_Float_Val()/Rres.get_Float_Val(), NULL, float_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}


/************* Methods for class plus_Ast ******************/
eval_Result plus_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an plus tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an plus tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result(Lres.get_Int_Val()+Rres.get_Int_Val(), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result(Lres.get_Float_Val()+Rres.get_Float_Val(), NULL, float_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}


/************* Methods for class minus_Ast ******************/
eval_Result minus_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an minus tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an minus tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result(Lres.get_Int_Val()-Rres.get_Int_Val(), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result(Lres.get_Float_Val()-Rres.get_Float_Val(), NULL, float_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}


/************* Methods for class unary_minus_Ast ******************/
eval_Result unary_minus_Ast::evaluate()
{
    CHECK_INVARIANT (ft != NULL, "child of an unary_minus tree node cannot be NULL")
    eval_Result i_res = ft->evaluate();

    eval_Result res = dummy_result;
    switch(i_res.which_Result()) {
        case int_Res:
            res = eval_Result(-i_res.get_Int_Val(), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result(-i_res.get_Float_Val(), NULL, float_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}

/************* Methods for class mult_Ast ******************/
eval_Result int_Ast::evaluate()
{
    eval_Result res(num, NULL, int_Res);
    return res;
}

/************* Methods for class mult_Ast ******************/
eval_Result float_Ast::evaluate()
{
    eval_Result res(fum, NULL, float_Res);
    return res;
}

/************* Methods for class geq_Ast ******************/
eval_Result geq_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an geq tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an geq tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result((int)(Lres.get_Int_Val()>=Rres.get_Int_Val()), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result((int)(Lres.get_Float_Val()>=Rres.get_Float_Val()), NULL, int_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}

/************* Methods for class leq_Ast ******************/
eval_Result leq_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an geq tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an geq tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result((int)(Lres.get_Int_Val()<=Rres.get_Int_Val()), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result((int)(Lres.get_Float_Val()<=Rres.get_Float_Val()), NULL, int_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}

/************* Methods for class gt_Ast ******************/
eval_Result gt_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an geq tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an geq tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result((int)(Lres.get_Int_Val()>Rres.get_Int_Val()), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result((int)(Lres.get_Float_Val()>Rres.get_Float_Val()), NULL, int_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}

/************* Methods for class lt_Ast ******************/
eval_Result lt_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an geq tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an geq tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result((int)(Lres.get_Int_Val()<Rres.get_Int_Val()), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result((int)(Lres.get_Float_Val()<Rres.get_Float_Val()), NULL, int_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}

/************* Methods for class eq_Ast ******************/
eval_Result eq_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an geq tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an geq tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result((int)(Lres.get_Int_Val()==Rres.get_Int_Val()), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result((int)(Lres.get_Float_Val()==Rres.get_Float_Val()), NULL, int_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}

/************* Methods for class neq_Ast ******************/
eval_Result neq_Ast::evaluate()
{
    CHECK_INVARIANT (left != NULL, "left child of an geq tree node cannot be NULL")
    eval_Result Lres = left->evaluate();

    CHECK_INVARIANT (right != NULL, "Right child of an geq tree node cannot be NULL")
    eval_Result Rres = right->evaluate();

    CHECK_INVARIANT(Lres.which_Result() == Rres.which_Result(), "value of left and right child of expression should be of same type")

    eval_Result res = dummy_result;
    switch(Lres.which_Result()) {
        case int_Res:
            res = eval_Result((int)(Lres.get_Int_Val()!=Rres.get_Int_Val()), NULL, int_Res);
            break;

        case float_Res:
            res = eval_Result((int)(Lres.get_Float_Val()!=Rres.get_Float_Val()), NULL, int_Res);
            break;

        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "value of expression can be either float or int");
            break;
    }
    return res;
}

/************* Methods for class goto_Ast ******************/
eval_Result goto_Ast::evaluate()
{
    int id = get_Int();
    eval_Result res(0, getPtrToId(id, NULL), next_BB_Res);
    print_Eval_Result(this);
    return res;
}

/************* Methods for class if_Ast ******************/
eval_Result if_Ast::evaluate()
{
    CHECK_INVARIANT (ft != NULL, "child of an unary_minus tree node cannot be NULL")
    eval_Result i_res = ft->evaluate();

    CHECK_INVARIANT (left != NULL, "left child of an geq tree node cannot be NULL")
    CHECK_INVARIANT (right != NULL, "Right child of an geq tree node cannot be NULL")

    eval_Result res = dummy_result;
    if(i_res.get_Int_Val() == 0) {
        res = eval_Result(0, getPtrToId(right->get_Int(), NULL), next_BB_Res);
    } else {
        res = eval_Result(0, getPtrToId(left->get_Int(), NULL), next_BB_Res);
    }

    print_Eval_Result(this);
    return res;
}

/************* Local functions ******************/
bb_Ptr getPtrToId(int id, bb_List_Ptr bb_lp)
{
    if(bb_lp == NULL) {bb_lp = program_object_P->get_Main_Proc_Ptr()->get_BB_List();}
    list<bb_Ptr>::iterator it;
    for (it=bb_lp->begin(); it!=bb_lp->end(); it++)
    {
        if((*it)->get_BB_Num() == id) {
            return *it;
        }
    }
    char mesg[100];
    sprintf(mesg, "Basic Block %d not found", id);
    report_Violation_of_Condition(SHOULD_NOT_REACH, mesg);
}
