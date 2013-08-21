
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
#include "icode.hh"

/****************************** Class ics_Opd *****************************/

opd_Category ics_Opd::get_Opd_Category() { return type;} 

reg_Desc_Ptr ics_Opd::get_Reg()              
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Reg method should not be called for a non-reg operand")
}

sym_Entry_Ptr ics_Opd::get_Sym_Entry() 
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Sym_Entry method should not be called for a non-address operand")
}

int ics_Opd::get_Num() 
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Num method should not be called for a non-constant operand")
}

double ics_Opd::get_Fum() 
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Fum method should not be called for a non-constant operand")
}

value_Type ics_Opd::get_Value_Type() 
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Value_Type method should not be called for a non-constant operand")
}
/****************************** Class mem_Addr_Opd *****************************/

mem_Addr_Opd::mem_Addr_Opd(sym_Entry_Ptr se_P) 
{
   sym_entry = se_P;
   type = mem_Addr;
}

sym_Entry_Ptr mem_Addr_Opd::get_Sym_Entry() 
{
    CHECK_INVARIANT(sym_entry, "Sym Entry of an address in an instruction cannot be NULL")
    return sym_entry;
}

mem_Addr_Opd& mem_Addr_Opd::operator=(const mem_Addr_Opd& rhs)
{
    type = rhs.type;     
    sym_entry = rhs.sym_entry;
    return *this;
}

value_Type mem_Addr_Opd::get_Value_Type()
{
  return sym_entry->get_Value_Type();
}


/****************************** Class reg_Addr_Opd *****************************/

reg_Addr_Opd::reg_Addr_Opd(reg_Desc_Ptr reg) 
{
   type = reg_Addr;
   reg_desc_ptr = reg;
}

reg_Desc_Ptr reg_Addr_Opd::get_Reg()    { return reg_desc_ptr; }

reg_Addr_Opd& reg_Addr_Opd::operator=(const reg_Addr_Opd& rhs)
{
    type = rhs.type;     
    reg_desc_ptr = rhs.reg_desc_ptr ;
    return *this;
}

value_Type reg_Addr_Opd::get_Value_Type()
{
  reg_Val_Type rtype = reg_desc_ptr->get_Reg_Value_Type();
  switch(rtype)
  {
    case int_Num :
      return int_Val;
      break;
    case float_Num :
      return float_Val;
      break;
    default:
      return int_Val;
      break;
  }
}


/****************************** Class const_Opd *****************************/

const_Opd::const_Opd(int n) 
{
   type = constant;
   num = n;
   val_type = int_Val;
}
const_Opd::const_Opd(double n) 
{
   type = constant;
   fum = n;
   val_type = float_Val;
}
int const_Opd::get_Num()     { return num; }

double const_Opd::get_Fum()  { return fum; }

const_Opd& const_Opd::operator=(const const_Opd& rhs)
{
    type = rhs.type;     
    num = rhs.num;
    fum = rhs.fum;
    return *this;
}
value_Type const_Opd::get_Value_Type()
{
  return val_type;
}

/****************************** Class icode_stmt *****************************/

inst_Desc_Ptr icode_Stmt::get_Operator()        { return op_desc_ptr; }

ics_Opd_Ptr icode_Stmt::get_Opd1()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "virtual method get_Opd1 not implemented")
}

ics_Opd_Ptr icode_Stmt::get_Opd2()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "virtual method get_Opd2 not implemented")
}

ics_Opd_Ptr icode_Stmt::get_Result()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "virtual method get_Result not implemented")
}

void icode_Stmt::set_Opd1(ics_Opd_Ptr io_P)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "virtual method set_Opd1 not implemented")
}

void icode_Stmt::set_Opd2(ics_Opd_Ptr io_P)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "virtual method set_Opd2 not implemented")
}

void icode_Stmt::set_Result(ics_Opd_Ptr io_P)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "virtual methos set_Result not implemented")
}



/*************************** Class move_IC_Stmt *****************************/

move_IC_Stmt::move_IC_Stmt(tgt_Op op, ics_Opd_Ptr o1, ics_Opd_Ptr res)
{ 
    op_desc_ptr = spim_inst_table[op];
    opd1 = o1;   
    result = res; 
}

ics_Opd_Ptr move_IC_Stmt::get_Opd1()          { return opd1; }
ics_Opd_Ptr move_IC_Stmt::get_Result()        { return result; }

void move_IC_Stmt::set_Opd1(ics_Opd_Ptr io_P)   { opd1 = io_P; }
void move_IC_Stmt::set_Result(ics_Opd_Ptr io_P) { result = io_P; }

move_IC_Stmt& move_IC_Stmt::operator=(const move_IC_Stmt& rhs)
{
    op_desc_ptr = rhs.op_desc_ptr;         
    opd1 = rhs.opd1;   
    result = rhs.result; 
    return *this;
}

/******************************Class compute_IC_Stmt****************************/

compute_IC_Stmt::compute_IC_Stmt(tgt_Op inst_op, ics_Opd_Ptr o1, ics_Opd_Ptr o2, ics_Opd_Ptr res)
{
    op_desc_ptr = spim_inst_table[inst_op];
    opd1 = o1;  
    opd2 = o2; 
    result = res; 
}

ics_Opd_Ptr compute_IC_Stmt::get_Opd1()          { return opd1; }
void compute_IC_Stmt::set_Opd1(ics_Opd_Ptr io_P) { opd1 = io_P; }
ics_Opd_Ptr compute_IC_Stmt::get_Opd2()          { return opd2; }
void compute_IC_Stmt::set_Opd2(ics_Opd_Ptr io_P) { opd2 = io_P; }
ics_Opd_Ptr compute_IC_Stmt::get_Result()        { return result; }
void compute_IC_Stmt::set_Result(ics_Opd_Ptr io_P) { result = io_P; }

/******************************** Class control_Flow_IC_Stmt************************/
int control_Flow_IC_Stmt::getBranchLabel()         {return branchlabel; }

/******************************* class condition_Branch_IC_Stmt*********************/
condition_Branch_IC_Stmt::condition_Branch_IC_Stmt(ics_Opd_Ptr opd1, ics_Opd_Ptr opd2, int branchl)
{
    op1 = opd1;
    op2 = opd2;
    branchlabel = branchl;
}
ics_Opd_Ptr condition_Branch_IC_Stmt::get_Opd1()          { return op1; }
void condition_Branch_IC_Stmt::set_Opd1(ics_Opd_Ptr io_P) { op1 = io_P; }
ics_Opd_Ptr condition_Branch_IC_Stmt::get_Opd2()          { return op2; }
void condition_Branch_IC_Stmt::set_Opd2(ics_Opd_Ptr io_P) { op2 = io_P; }  

/*******************************class uncondition_Branch_IC_Stmt***********************/
uncondition_Branch_IC_Stmt::uncondition_Branch_IC_Stmt(int branchl)
{
    branchlabel = branchl;
}

/******************************* Class code_for_Ast ****************************/

code_for_Ast::code_for_Ast(reg_Desc_Ptr reg, icode_Stmt_List ic_L)
{
    ics_List = ic_L;
    result_reg = reg;
}

void code_for_Ast::append_ICS(icode_Stmt_Ptr ics_P)
{
    ics_List.push_back(ics_P);

    ics_Opd_Ptr result = ics_P->get_Result();

    result_reg = result->get_Reg();
}

icode_Stmt_List code_for_Ast::get_Icode()  { return ics_List; }

reg_Desc_Ptr code_for_Ast::get_Result_Reg() {return result_reg;}

code_for_Ast& code_for_Ast::operator=(const code_for_Ast& rhs)
{
    ics_List = rhs.ics_List;
    result_reg = rhs.result_reg;
    return *this;
}

/************************ class instruction_Descriptor ********************************/

tgt_Op instruction_Descriptor::get_Operator()                   { return inst_op; }
string instruction_Descriptor::get_Name()                       { return name; }
string instruction_Descriptor::get_Mnemonic()                   { return mnemonic; }
string instruction_Descriptor::get_IC_Symbol()                  { return ic_symbol; }
icode_Format instruction_Descriptor::get_IC_Format()            { return ic_format; }
assembly_Format instruction_Descriptor::get_Assembly_Format()   { return a_format; }

void instruction_Descriptor::print_Instruction_Descriptor()
{
    string af, icf, ops;

    switch (a_format)
    {
        case a_op_r_o1: af = "a_op_r_o1"; break; 
        default: CHECK_INVARIANT(SHOULD_NOT_REACH, "Assembly format not supported") break;
    }

    switch (ic_format)
    {
        case i_r_op_o1: icf = "i_op_r_o1"; break; 
        default: CHECK_INVARIANT(SHOULD_NOT_REACH, "Intermediate code format not supported") break;
    }

    switch(inst_op)
    {
        case load : ops = "load"; break;
        case store : ops = "store"; break;
        case imm_Load : ops = "imm_Load"; break;
        default: CHECK_INVARIANT(SHOULD_NOT_REACH, "Target operator not supported") break;
    }
    cout << "Operator " << ops << " Mnemonic " << mnemonic << " IC symbol " 
         << ic_symbol << " IC format " << icf << " Assembly format " << af;
}

instruction_Descriptor::instruction_Descriptor (tgt_Op op, string nm, string mnc, 
                                  string ics, icode_Format icf, assembly_Format af)
{
    inst_op = op;
    name = nm; 
    mnemonic = mnc;
    ic_symbol = ics;
    ic_format = icf;
    a_format = af;
}

/******************************* global functions and data for instructions **********************************/

void initialize_Inst_Table()
{
    spim_inst_table[store] = 		
          new instruction_Descriptor(store,	"store", 	"sw", "", 	i_r_op_o1, 	a_op_o1_r);
    spim_inst_table[load] = 		
          new instruction_Descriptor(store,	"load", 	"lw", "",	i_r_op_o1, 	a_op_r_o1);
    spim_inst_table[imm_Load] = 	
          new instruction_Descriptor(imm_Load,	"iLoad",	"li", "",	i_r_op_o1, 	a_op_r_o1);
    spim_inst_table[add] =   
          new instruction_Descriptor(add,  "add",  "add", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[sub] =   
          new instruction_Descriptor(sub,  "sub",  "sub", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[mult] =   
          new instruction_Descriptor(mult,  "mult",  "mult", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[div_op] =   
          new instruction_Descriptor(div_op,  "div",  "div", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[uminus] =   
          new instruction_Descriptor(uminus,  "uminus",  "neg", "", i_r_op_o1,  a_op_r_o1);
    spim_inst_table[gt] =   
          new instruction_Descriptor(gt,  "sgt",  "sgt", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[lt] =   
          new instruction_Descriptor(lt,  "slt",  "slt", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[geq] =   
          new instruction_Descriptor(geq,  "sge",  "sge", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[leq] =   
          new instruction_Descriptor(leq,  "sle",  "sle", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[eq] =   
          new instruction_Descriptor(eq,  "seq",  "seq", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    spim_inst_table[neq] =   
          new instruction_Descriptor(neq,  "sne",  "sne", "", i_r_o1_op_o2,  a_op_r_o1_o2);
    
}

void print_Inst_Table()
{
    map<tgt_Op, inst_Desc_Ptr>::iterator i;
    for (i = spim_inst_table.begin(); i != spim_inst_table.end(); i++)
            i->second->print_Instruction_Descriptor();
}

inst_Table spim_inst_table;

