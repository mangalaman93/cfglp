
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
#include <string>
#include <vector>
#include <list>
#include <map>

using namespace std;

#include "common-classes.hh"
#include "evaluate.hh"
#include "support.hh"

#include "reg-alloc.hh"
#include "symtab.hh"
#include "ast.hh"
#include "program.hh"

reg_Table spim_reg_table;

register_Descriptor::register_Descriptor(spim_Reg reg, string s, reg_Val_Type vt, reg_Use_Category uc)
{
    reg_id = reg;
    reg_name = s;
    value_type = vt;
    reg_use = uc; 
    used_for_expr_result = false;
    is_live = false;
}

void register_Descriptor::print_Register_Descriptor()
{
    string uc;

    switch (reg_use)
    {
        case gp_data: 	 uc = "gp_data"; break;
        case argument: 	 uc = "argument";break;
        case pointer: 	 uc = "pointer";break;
        case fixed_reg:  uc ="fixed";break;
        case ret_address:uc ="ret_address";break;
        case fn_result:	 uc ="fn_result";break;
        default: CHECK_INVARIANT(SHOULD_NOT_REACH, "Wrong usage category") break;
    }
    cout << "Reg Name: " << reg_name << " Usage category " << uc << "\n";
}


reg_Use_Category register_Descriptor::get_Use_Category() { return reg_use; }

spim_Reg register_Descriptor::get_Reg()                  { return reg_id; }

string register_Descriptor::get_Name()                   { return reg_name; }

void register_Descriptor::set_Alive()                    { is_live = true; }

void register_Descriptor::reset_Alive()                  { is_live = false; }

bool register_Descriptor::is_Alive()                     { return is_live; }

list<sym_Entry_Ptr> register_Descriptor::get_Lra_Sym_List()                   { return lra_sym_list; }

reg_Val_Type register_Descriptor::get_Reg_Value_Type()   { return value_type;}

bool register_Descriptor::is_Sym_List_Empty()            { return lra_sym_list.empty(); }

bool register_Descriptor::used_for_Expr_Result()         { return used_for_expr_result; }

void register_Descriptor::set_Use_for_Expr_Result()     
{
    CHECK_INVARIANT(!used_for_expr_result, "register has been already allocated to store some other expression")
    used_for_expr_result = true;
}

void register_Descriptor::reset_Use_for_Expr_Result()     { used_for_expr_result = false; }

bool register_Descriptor::is_Free()         
{ 
    if ((reg_use == gp_data) && (lra_sym_list.empty()) && (used_for_expr_result == false))
        return true;
    else 
        return false;
}

void register_Descriptor::remove_Sym_Entry_from_List(sym_Entry_Ptr sep)
{
    lra_sym_list.remove(sep);
}

bool register_Descriptor::find_Sym_Entry_in_List(sym_Entry_Ptr sep)
{
   list<sym_Entry_Ptr>::iterator i;
    for (i = lra_sym_list.begin(); i != lra_sym_list.end(); i++)
        if (*i == sep)
          return true;

    return false;
}

    void clear_Sym_List();

void register_Descriptor::clear_lra_Sym_List()
{
   list<sym_Entry_Ptr>::iterator i;
    for (i = lra_sym_list.begin(); i != lra_sym_list.end(); i++)
    {
        sym_Entry_Ptr sep = *i;
        sep->set_Reg(NULL);
    }
    lra_sym_list.clear();
}

void register_Descriptor::update_Sym_Info(sym_Entry_Ptr sep)
{
    if (find_Sym_Entry_in_List(sep) == false)
        lra_sym_list.push_back(sep);
}

void print_Reg_Table()
{
    map<spim_Reg, reg_Desc_Ptr>::iterator i;
    for (i = spim_reg_table.begin(); i != spim_reg_table.end(); i++)
            i->second->print_Register_Descriptor();
}


void initialize_Reg_Table()
{

    spim_reg_table[zero]= new register_Descriptor(	zero,	"zero", 	int_Num, 	fixed_reg);
    spim_reg_table[v0]	= new register_Descriptor(	v0,	"v0", 		int_Num, 	gp_data);
    spim_reg_table[v1]	= new register_Descriptor(	v1,	"v1", 		int_Num, 	fn_result);
    spim_reg_table[a0]	= new register_Descriptor(	a0,	"a0", 		int_Num, 	argument);
    spim_reg_table[a1]	= new register_Descriptor(	a1,	"a1", 		int_Num, 	argument);
    spim_reg_table[a2]	= new register_Descriptor(	a2,	"a2", 		int_Num, 	argument);
    spim_reg_table[a3]	= new register_Descriptor(	a3,	"a3", 		int_Num, 	argument);
    spim_reg_table[t0]	= new register_Descriptor(	t0,	"t0", 		int_Num, 	gp_data);
    spim_reg_table[t1]	= new register_Descriptor(	t1,	"t1", 		int_Num, 	gp_data);
    spim_reg_table[t2]	= new register_Descriptor(	t2,	"t2", 		int_Num, 	gp_data);
    spim_reg_table[t3]	= new register_Descriptor(	t3,	"t3", 		int_Num, 	gp_data);
    spim_reg_table[t4]	= new register_Descriptor(	t4,	"t4", 		int_Num, 	gp_data);
    spim_reg_table[t5]	= new register_Descriptor(	t5,	"t5", 		int_Num, 	gp_data);
    spim_reg_table[t6]	= new register_Descriptor(	t6,	"t6", 		int_Num, 	gp_data);
    spim_reg_table[t7]	= new register_Descriptor(	t7,	"t7", 		int_Num, 	gp_data);
    spim_reg_table[t8]	= new register_Descriptor(	t8,	"t8", 		int_Num, 	gp_data);
    spim_reg_table[t9]	= new register_Descriptor(	t9,	"t9", 		int_Num, 	gp_data);
    spim_reg_table[f0]  = new register_Descriptor(  f0, "f0",       float_Num,    gp_data);
    spim_reg_table[f1]  = new register_Descriptor(  f1, "f1",       float_Num,    gp_data);
    spim_reg_table[f2]  = new register_Descriptor(  f2, "f2",       float_Num,    gp_data);
    spim_reg_table[f3]  = new register_Descriptor(  f3, "f3",       float_Num,    gp_data);
    spim_reg_table[f4]  = new register_Descriptor(  f4, "f4",       float_Num,    gp_data);
    spim_reg_table[f5]  = new register_Descriptor(  f5, "f5",       float_Num,    gp_data);
    spim_reg_table[f6]  = new register_Descriptor(  f6, "f6",       float_Num,    gp_data);
    spim_reg_table[f7]  = new register_Descriptor(  f7, "f7",       float_Num,    gp_data);
    spim_reg_table[f8]  = new register_Descriptor(  f8, "f8",       float_Num,    gp_data);
    spim_reg_table[f9]  = new register_Descriptor(  f9, "f9",       float_Num,    gp_data);
    spim_reg_table[s0]	= new register_Descriptor(	s0,	"s0", 		int_Num, 	gp_data);
    spim_reg_table[s1]	= new register_Descriptor(	s1,	"s1", 		int_Num, 	gp_data);
    spim_reg_table[s2]	= new register_Descriptor(	s2,	"s2", 		int_Num, 	gp_data);
    spim_reg_table[s3]	= new register_Descriptor(	s3,	"s3", 		int_Num, 	gp_data);
    spim_reg_table[s4]	= new register_Descriptor(	s4,	"s4", 		int_Num, 	gp_data);
    spim_reg_table[s5]	= new register_Descriptor(	s5,	"s5", 		int_Num, 	gp_data);
    spim_reg_table[s6]	= new register_Descriptor(	s6,	"s6", 		int_Num, 	gp_data);
    spim_reg_table[s7]	= new register_Descriptor(	s7,	"s7", 		int_Num, 	gp_data);
    spim_reg_table[gp]	= new register_Descriptor(	gp,	"gp", 		int_Num, 	pointer);
    spim_reg_table[sp]	= new register_Descriptor(	sp,	"sp", 		int_Num, 	pointer);
    spim_reg_table[fp]	= new register_Descriptor(	fp,	"fp", 		int_Num, 	pointer);
    spim_reg_table[ra]	= new register_Descriptor(	ra,	"ra", 		int_Num, 	ret_address);

}



lra_Outcome::lra_Outcome(reg_Desc_Ptr rdp, bool nr, bool sr, bool dr, bool mv, bool ld)
{
    reg_desc_ptr = rdp;
    is_a_new_reg = nr;
    is_same_as_source = sr;
    is_same_as_destination = dr;
    reg_move_needed = mv; 
    load_needed = ld;
}

reg_Desc_Ptr lra_Outcome::get_Reg() { return reg_desc_ptr; }
bool lra_Outcome::is_New_Reg()      { return is_a_new_reg; }
bool lra_Outcome::is_Source_Reg()   { return is_same_as_source; }
bool lra_Outcome::is_Dest_Reg()     { return is_same_as_destination; }
bool lra_Outcome::is_Mov_Needed()      { return reg_move_needed;  }
bool lra_Outcome::is_Load_Needed()     { return load_needed; }

lra_Outcome allocate_Local_Registers(lra_Scenario lcase, ast_Ptr dest_mem, ast_Ptr source_mem)
{
#if 0
    //spim_Reg dest_reg, src_reg, res_reg;
    reg_Desc_Ptr dest_reg, src_reg, res_reg;
    bool is_a_new_reg, is_same_as_source, is_same_as_destination, reg_move_needed, load_needed;
    sym_Entry_Ptr ssep, dsep;

    ssep = dsep = NULL;
    dest_reg = src_reg = res_reg = NULL;

    is_a_new_reg = is_same_as_source = is_same_as_destination = reg_move_needed = load_needed = false;

    //dest_reg = src_reg = res_reg = none;

    switch (lcase)
    {
        case m2m:
            CHECK_INVARIANT(dest_mem, "Destination ast pointer cannot be NULL for m2m scenario in lra")
            CHECK_INVARIANT(source_mem, "Sourse ast pointer cannot be NULL for m2m scenario in lra")

            dsep = dest_mem->get_Sym_Entry();
            CHECK_INVARIANT(dsep, "Sym Entry of destination ast cannot be NULL for m2m scenario in lra")
            dest_reg = dsep->get_Reg(); 

            ssep = source_mem->get_Sym_Entry();
            CHECK_INVARIANT(ssep, "Sym Entry of source ast cannot be NULL for m2m scenario in lra")
            src_reg = ssep->get_Reg(); 

            if (src_reg != NULL)
            {
                res_reg = src_reg;
                is_same_as_source = true;
            }
            else if (dest_reg != NULL)
            {
                res_reg = dest_reg;
                is_same_as_destination = true;
                load_needed = true;
            }
            else 
            {
                res_reg = get_New_Reg();
                load_needed = true;
            }
            break;
        case m2r:
            CHECK_INVARIANT(source_mem, "Sourse ast pointer cannot be NULL for m2r scenario in lra")

            ssep = source_mem->get_Sym_Entry();
            CHECK_INVARIANT(ssep, "Sym Entry of source ast cannot be NULL for m2m scenario in lra")
            src_reg = ssep->get_Reg(); 

            if (src_reg != NULL)
            {
                res_reg = src_reg;
                is_same_as_source = true;
            }
            else 
            {
                res_reg = get_New_Reg();
                load_needed = true;
            }
            break;
        case r2m:
            CHECK_INVARIANT(SHOULD_NOT_REACH,"r2m scenario does not call for local register allocation")
            break;
        case c2m:
            CHECK_INVARIANT(dest_mem, "Destination ast pointer cannot be NULL for c2m scenario in lra")

            dsep = dest_mem->get_Sym_Entry();
            CHECK_INVARIANT(dsep, "Sym Entry of destination ast cannot be NULL for m2m scenario in lra")
            dest_reg = dsep->get_Reg(); 

            if (dest_reg != NULL)is_Free
            {
                res_reg = dest_reg;
                is_same_as_destination = true;
                load_needed = true;
            }
            else 
            {
                res_reg = get_New_Reg();
                load_needed = true;
            }
            break;
        case c2r:
            res_reg = get_New_Reg();
            load_needed = true;
            break;
        case r2r:
             CHECK_INVARIANT(SHOULD_NOT_REACH,"r2r scenario does not call for local register allocation")
            break;
        default:
             CHECK_INVARIANT(SHOULD_NOT_REACH,"Illegal local register allocation scenario")
            break;
    }
    
    lra_Outcome lrao (res_reg, is_a_new_reg, is_same_as_source, is_same_as_destination, 
                      reg_move_needed, load_needed); 

    CHECK_INVARIANT (res_reg != NULL && dsep != NULL, "Inconsistent information in lra");

    if (dest_reg)
        free_Reg(dest_reg, dsep); /* dest_reg is the older reg of destination */
    update_Reg_Sym_Mappings(res_reg, dsep);

    return lrao;
#endif
}

reg_Desc_Ptr get_New_Reg(value_Type val_type)
{
    //spim_Reg reg = none;
    reg_Val_Type reg_val_type;
    sym_Entry_Ptr tsep;
    list<sym_Entry_Ptr> llist; 
    reg_Desc_Ptr rdp = NULL;
    switch(val_type)
    {
        case int_Val:
            reg_val_type = int_Num;
            break;
        case float_Val:
            reg_val_type = float_Num;
            break;
        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH,"register can only be allocated to integer or float variables")
    }

    map<spim_Reg, reg_Desc_Ptr>::iterator i;
    for (i = spim_reg_table.begin(); i != spim_reg_table.end(); i++)
    {
        rdp = i->second;

        CHECK_INVARIANT(rdp != NULL, "Null Register Descriptor in the register table");

        if (rdp->is_Free() && rdp->get_Reg_Value_Type() == reg_val_type)
        {
            return rdp;
        }
             
    }
    //CHECK_INVARIANT(SHOULD_NOT_REACH, "Error in get_New_Reg or register requirements of input program cannot be met");
    //freeing register as not register is found free
    for (i = spim_reg_table.begin(); i != spim_reg_table.end(); i++)
    {
        rdp = i->second;
        llist = rdp->get_Lra_Sym_List(); 
        CHECK_INVARIANT(rdp != NULL, "Null Register Descriptor in the register table");
        if(!rdp->is_Free() && !rdp->is_Alive())
        {
            list<sym_Entry_Ptr>::iterator i;
            for (i=llist.begin(); i!=llist.end(); i++)
            {
                tsep = (*i);
                rdp->remove_Sym_Entry_from_List(tsep);
                tsep->set_Reg(NULL);
            }
            rdp->reset_Use_for_Expr_Result();
        }
        
    }
    return get_New_Reg(val_type);
}

void free_Reg(reg_Desc_Ptr dest_rdp, ast_Ptr dest_ast, bool do_lra)
{
    CHECK_INVARIANT(dest_rdp, "The register descriptor of the destination should not be NULL while freeing a register")
    /* Remove the destination from its register descriptor */
   
    switch(dest_ast->get_Tree_Op())
    {
        case name_Leaf:
            if(!do_lra)
            {
                dest_rdp->remove_Sym_Entry_from_List(dest_ast->get_Sym_Entry());
                (dest_ast->get_Sym_Entry())->set_Reg(NULL);
                dest_rdp->reset_Use_for_Expr_Result();
            }
            break;
        case int_Leaf:
        case float_Leaf:
        case plus_node:
        case minus_node:
        case mult_node:
        case unary_minus_node:
        case div_node:
        case gt_node:
        case lt_node:
        case geq_node:
        case leq_node:
        case eq_node:
        case neq_node:
             CHECK_INVARIANT(dest_rdp->used_for_Expr_Result(), "cannot free already freed register")
             dest_rdp->reset_Use_for_Expr_Result();
             break;
        default:
            CHECK_INVARIANT(SHOULD_NOT_REACH, "free register called on non-value ast node")
            break;
    }
}

#if 0
spim_Reg get_New_Reg()
{
    spim_Reg reg = none;

    map<spim_Reg, reg_Desc_Ptr>::iterator i;
    for (i = spim_reg_table.begin(); i != spim_reg_table.end(); i++)
    {
        reg_Desc_Ptr rdp = i->second;

        if ((rdp->get_Use_Category() == gp_data) && 
            (rdp->is_Sym_List_Empty()))
           reg = rdp->get_Reg();
    }
    CHECK_INVARIANT(reg == none, "Error in get_New_Reg or register requirements of input program cannot be met");
    return reg;
}
#endif

void update_Reg_Sym_Mappings(reg_Desc_Ptr res_rdp, sym_Entry_Ptr dest_sym)
{
    CHECK_INVARIANT(dest_sym, "Destination sym should not be NULL while updating register information")
    CHECK_INVARIANT(res_rdp, "The register descriptor of the result should not be NULL while updating register information")

 //   reg_Desc_Ptr dest_rdp = dest_sym->get_Reg();

 //   CHECK_INVARIANT (dest_rdp == NULL, "The destination register should have been freed")

    /* set the register of the destination as the new register */
    dest_sym->set_Reg(res_rdp);
    
    /* add the destination to the list of sym of the register */
    res_rdp->update_Sym_Info(dest_sym);
}


void clear_Local_Reg_Mappings()
{
    /* For each register
          For it sym in lra_sym_list
             remove the sym from the list
             set the reg_desc_ptr of the sym to NULL
    */

    map<spim_Reg, reg_Desc_Ptr>::iterator i;
    for (i = spim_reg_table.begin(); i != spim_reg_table.end(); i++)
    {
        reg_Desc_Ptr rdp = i->second;
        if(rdp->is_Alive()){
            rdp->reset_Alive();
        }
        rdp->clear_lra_Sym_List();
        rdp->reset_Use_for_Expr_Result();
    }

   /* 
      Note that we do not need to save values at the end
      of a basic block because the values have already been
      saved for each assignment statement. Any optimization
      that tries to postpone the store statements may have to 
      consider storing all unstored values at the end of
      a basic block.
   */
}

void validate_Init_Local_Reg_Mappings()
{
    map<spim_Reg, reg_Desc_Ptr>::iterator i;
    for (i = spim_reg_table.begin(); i != spim_reg_table.end(); i++)
    {
        reg_Desc_Ptr rdp = i->second;
        if (rdp->get_Use_Category() == gp_data)
        {
           CHECK_INVARIANT(rdp->is_Free(), "GP data registers should be free at the start of a basic block") 
        }
            
    }
}
