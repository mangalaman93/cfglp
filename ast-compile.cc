
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
#include "icode.hh"


ast_Code_Ptr asgn_Ast::compile()
{
    /* 
       An assignment x = y where y is a variable is compiled as a combination of load and
       store statements:
       (load) R <- y 
       (store) x <- R
       If y is a constant, the statement is compiled as 
       (imm_Load) R <- y 
       (store) x <- R
       where imm_Load denotes the load immediate operation.
    */

    ast_Code_Ptr ast_code, right_code; 
    ics_Opd_Ptr mem_opd, reg_opd;
    reg_Desc_Ptr source_reg, load_reg, dest_reg;
    icode_Stmt_Ptr store_stmt; 
    sym_Entry_Ptr dest_sym;

    bool do_lra = cmd_options.do_Lra();

    ast_code = right_code = NULL;
    dest_sym = NULL;
    store_stmt = NULL;
    mem_opd = reg_opd = NULL;
    load_reg = dest_reg = NULL;

    icode_Stmt_List ic_L;
    CHECK_INVARIANT (right != NULL, "Right child of an assignment tree node cannot be NULL")

    dest_sym = left->get_Sym_Entry();
    dest_reg = dest_sym->get_Reg(); 
    if (dest_reg != NULL) {
        free_Reg(dest_reg, left, false);
    }

    /*  
        The load instruction is generated for the right hand side. 
        The resulting register is used in the store instruction for
        for the left hand side.
    */

    right_code = right->compile();
    load_reg = right_code->get_Result_Reg();
    reg_opd = new reg_Addr_Opd(load_reg);
    list<icode_Stmt_Ptr> temp = right_code->get_Icode();
    ic_L.splice(ic_L.end(), temp);
    load_reg->reset_Alive();
    /* 
       Now generate the store in destination using the 
       reg_opd created above 
    */
  
    CHECK_INVARIANT (left != NULL, "Left child of an assignment tree node cannot be NULL")
    CHECK_INVARIANT (left->get_Tree_Op() == name_Leaf, "LHS of an assignment should be a name")

    update_Reg_Sym_Mappings(load_reg, dest_sym);
    mem_opd = new mem_Addr_Opd(dest_sym);
    store_stmt = new move_IC_Stmt(store, reg_opd, mem_opd);

    /* 
       Create the object to be returned by joining the load and 
       store statements. When we include the compute operations,
       we will have to suffix these load and store statements to
       the statements generated for the right hand side.
    */

    if (store_stmt)
    	ic_L.push_back(store_stmt);

    free_Reg(dest_sym->get_Reg(), left, do_lra);
    ast_code = new code_for_Ast(load_reg, ic_L);
    return ast_code;
}

ast_Code_Ptr unary_op_Ast::compile()
{
    ast_Code_Ptr ast_code, ft_code;
    ics_Opd_Ptr reg_opd1, reg_opd;
    reg_Desc_Ptr op_reg;
    icode_Stmt_Ptr op_stmt;

    bool do_lra = cmd_options.do_Lra();
    icode_Stmt_List ic_L;

    ast_code = ft_code = NULL;
    reg_opd1 = reg_opd = NULL;
    op_reg = NULL;
    op_stmt = NULL;

    tgt_Op Op;
    switch(t_op) {
        case unary_minus_node:
            Op = uminus;
            break;
        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "NOT POSSIBLE :-o")
            break;
    }
 
    ft_code = ft->compile();
    op_reg = get_New_Reg(get_Val_Type());
    reg_opd = new reg_Addr_Opd(op_reg);
    reg_opd1 = new reg_Addr_Opd(ft_code->get_Result_Reg());
    op_stmt = new compute_IC_Stmt(Op, reg_opd1, NULL, reg_opd);
    op_reg->set_Use_for_Expr_Result();

    op_reg->set_Alive();
    (ft_code->get_Result_Reg())->reset_Alive();
    free_Reg(reg_opd1->get_Reg(), ft, do_lra);

    list<icode_Stmt_Ptr> temp = ft_code->get_Icode();
    ic_L.splice(ic_L.end(), temp);
    if (op_stmt)
        ic_L.push_back(op_stmt);
    
    ast_code = new code_for_Ast(op_reg, ic_L);
    return ast_code;
}

ast_Code_Ptr binary_op_Ast::compile()
{
    ast_Code_Ptr ast_code, left_code, right_code; 
    ics_Opd_Ptr reg_opd1, reg_opd2, reg_opd;
    reg_Desc_Ptr op_reg;
    icode_Stmt_Ptr op_stmt;

    bool do_lra = cmd_options.do_Lra();
    icode_Stmt_List ic_L;

    ast_code = left_code = right_code = NULL;
    reg_opd1 = reg_opd2 = reg_opd = NULL;
    op_reg = NULL;
    op_stmt = NULL;

    tgt_Op Op;
    switch(t_op) {
        case plus_node:
            Op = add;
            break;
        case minus_node:
            Op = sub;
            break;
        case mult_node:
            Op = mult;
            break;
        case div_node:
            Op = div_op;
            break;
        case gt_node:
            Op = gt;
            break;
        case lt_node:
            Op = lt;
            break;
        case geq_node:
            Op = geq;
            break;
        case leq_node:
            Op = leq;
            break;
        case eq_node:
            Op = eq;
            break;
        case neq_node:
            Op = neq;
            break;
        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "NOT POSSIBLE :-o")
            break;
    }

    left_code = left->compile();
    reg_opd1 = new reg_Addr_Opd(left_code->get_Result_Reg());
    right_code = right->compile();
    reg_opd2 = new reg_Addr_Opd(right_code->get_Result_Reg());
    op_reg = get_New_Reg(get_Val_Type());
    reg_opd = new reg_Addr_Opd(op_reg);
    op_stmt = new compute_IC_Stmt(Op, reg_opd1, reg_opd2, reg_opd);
    op_reg->set_Use_for_Expr_Result();

    op_reg->set_Alive();
    (left_code->get_Result_Reg())->reset_Alive();
    (right_code->get_Result_Reg())->reset_Alive();

    free_Reg(reg_opd1->get_Reg(), left, false);
    free_Reg(reg_opd2->get_Reg(), right, false);

    list<icode_Stmt_Ptr> temp = left_code->get_Icode();
    ic_L.splice(ic_L.end(), temp);
    temp = right_code->get_Icode();
    ic_L.splice(ic_L.end(), temp);
    if (op_stmt)
        ic_L.push_back(op_stmt);
    
    ast_code = new code_for_Ast(op_reg, ic_L);
    return ast_code;
}

ast_Code_Ptr name_Ast::compile()
{
    ast_Code_Ptr ast_code; 
    ics_Opd_Ptr reg_opd, opd1;
    reg_Desc_Ptr load_reg;
    icode_Stmt_Ptr load_stmt; 
    sym_Entry_Ptr source_sym;

    bool do_lra = cmd_options.do_Lra();
    icode_Stmt_List ic_L;

    ast_code = NULL;
    source_sym = NULL;
    load_stmt = NULL;
    reg_opd = opd1 = NULL;
    load_reg = NULL;

    source_sym = get_Sym_Entry();
    load_reg = source_sym->get_Reg(); 
    if (!do_lra || load_reg == NULL)
    {
        opd1 = new mem_Addr_Opd(source_sym);
        load_reg = get_New_Reg(get_Val_Type());
        reg_opd = new reg_Addr_Opd(load_reg);
        load_stmt = new move_IC_Stmt(load, opd1,reg_opd);
        update_Reg_Sym_Mappings(load_reg, source_sym);
    }
    load_reg->set_Alive();
    if (load_stmt)
        ic_L.push_back(load_stmt);
    
    ast_code = new code_for_Ast(load_reg, ic_L);
    return ast_code;
}

ast_Code_Ptr int_Ast::compile()
{
    ast_Code_Ptr ast_code; 
    ics_Opd_Ptr reg_opd, opd1;
    reg_Desc_Ptr load_reg;
    icode_Stmt_Ptr load_stmt;

    bool do_lra = cmd_options.do_Lra();
    icode_Stmt_List ic_L;

    ast_code = NULL;
    load_stmt = NULL;
    reg_opd = opd1 = NULL;
    load_reg = NULL;

    load_reg = get_New_Reg(get_Val_Type());
    load_reg->set_Alive();
    load_reg->set_Use_for_Expr_Result();

    reg_opd = new reg_Addr_Opd(load_reg);
    opd1 = new const_Opd(get_Int());
    load_stmt = new move_IC_Stmt(imm_Load, opd1,reg_opd);
    
    if (load_stmt)
        ic_L.push_back(load_stmt);
    
    ast_code = new code_for_Ast(load_reg, ic_L);
    return ast_code;
}

ast_Code_Ptr float_Ast::compile()
{
    ast_Code_Ptr ast_code; 
    ics_Opd_Ptr reg_opd, opd1;
    reg_Desc_Ptr load_reg;
    icode_Stmt_Ptr load_stmt;

    bool do_lra = cmd_options.do_Lra();
    icode_Stmt_List ic_L;

    ast_code = NULL;
    load_stmt = NULL;
    reg_opd = opd1 = NULL;
    load_reg = NULL;

    load_reg = get_New_Reg(get_Val_Type());
    load_reg->set_Alive();
    load_reg->set_Use_for_Expr_Result();

    reg_opd = new reg_Addr_Opd(load_reg);
    opd1 = new const_Opd(get_Float());
    load_stmt = new move_IC_Stmt(imm_Load, opd1,reg_opd);

    if (load_stmt)
        ic_L.push_back(load_stmt);
    
    ast_code = new code_for_Ast(load_reg, ic_L);
    return ast_code;
}

ast_Code_Ptr goto_Ast::compile()
{
    ast_Code_Ptr ast_code;
    icode_Stmt_Ptr goto_stmt;

    bool do_lra = cmd_options.do_Lra();
    icode_Stmt_List ic_L;

    ast_code = NULL;
    goto_stmt = NULL;

    goto_stmt = new uncondition_Branch_IC_Stmt(num);
    ic_L.push_back(goto_stmt);

    ast_code = new code_for_Ast(NULL, ic_L);
    return ast_code;
}

ast_Code_Ptr if_Ast::compile()
{
    ast_Code_Ptr ast_code, cond_code;
    icode_Stmt_Ptr if_stmt, goto_stmt;
    ics_Opd_Ptr reg_opd;
    reg_Desc_Ptr load_reg;

    bool do_lra = cmd_options.do_Lra();

    ast_code = cond_code = NULL;
    if_stmt = goto_stmt = NULL;
    reg_opd = NULL;
    load_reg = NULL;

    icode_Stmt_List ic_L;

    cond_code = ft->compile();
    load_reg = cond_code->get_Result_Reg();
    reg_opd = new reg_Addr_Opd(load_reg);
    list<icode_Stmt_Ptr> temp = cond_code->get_Icode();
    ic_L.splice(ic_L.end(), temp);
    free_Reg(load_reg, ft, do_lra);

    if_stmt = new condition_Branch_IC_Stmt(reg_opd, new reg_Addr_Opd(spim_reg_table[zero]), left->get_Int());
    goto_stmt = new uncondition_Branch_IC_Stmt(right->get_Int());
    ic_L.push_back(if_stmt);
    ic_L.push_back(goto_stmt);

    ast_code = new code_for_Ast(NULL, ic_L);
    return ast_code;
}

ast_Code_Ptr ast_Node::compile()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "compile method cannot be called on a non-asgn-Ast")
}

