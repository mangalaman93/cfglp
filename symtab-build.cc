
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
#include <cstdlib>
#include <string>
#include <vector>
#include <list>

using namespace std;

#include "common-classes.hh"
#include "evaluate.hh"
#include "reg-alloc.hh"
#include "symtab.hh"
#include "ast.hh"
#include "support.hh"
#include "program.hh"

int get_Size_of_Value_Type(value_Type vt);

/********************************* sym_Entry ******************************/

string sym_Entry::get_Name()               { return name; }
int sym_Entry::get_Line_Number()           { return lineno; }
/********************************* sym_Entry_for_Var ******************************/

value_Type sym_Entry_for_Var::get_Value_Type()
{
    string mesg = "The value type of variable " + name + " should have been int_Val or float_Val";
    CHECK_INVARIANT (type == int_Val || type == float_Val, mesg)
    return type;
} 

sym_Scope sym_Entry_for_Var::get_Sym_Scope()
{
    string mesg = "The scope of variable " + name + " should have been gloabal or local";
    CHECK_INVARIANT (sym_scope == is_Global || sym_scope == is_Local, mesg)
    return sym_scope;
} 


entity_Type sym_Entry_for_Var::get_Entity_Type()
{
    string mesg = "The entity type of name " + name + " should have been variable";
    CHECK_INVARIANT (en_type == entity_Var, mesg)
    return en_type;
} 

int sym_Entry_for_Var::get_Start_Offset()         { return start_offset;    }

int sym_Entry_for_Var::get_End_Offset()           { return end_offset;    }

void sym_Entry_for_Var::set_Start_Offset(int num) { start_offset = num;    }

void sym_Entry_for_Var::set_End_Offset(int num)   { end_offset = num;    }

bool sym_Entry_for_Var::is_Undefined()            { return undefined; }

void sym_Entry_for_Var::reset_Undefined_Status()  { undefined = false; }

void sym_Entry_for_Var::set_Reg(reg_Desc_Ptr r)   { reg_desc_ptr = r; }

reg_Desc_Ptr sym_Entry_for_Var::get_Reg()         { return reg_desc_ptr; }
/********************************* sym_Entry_for_Float_Var ******************************/
sym_Entry_for_Float_Var::sym_Entry_for_Float_Var(string s, int line)
{
    name = s;
    en_type = entity_Var;
    type = float_Val;
    start_offset = end_offset = 0;
    fvalue = 0;
    lineno = line;
    reg_desc_ptr = NULL;
     
    symtab_Stack_Top top = symtab_in_scope_P->get_Stack_Top();
   
    if (top == global)
    {
        undefined = false;
        sym_scope = is_Global;
    }
    else if (top == local)
    {
        undefined = true;
        sym_scope = is_Local;
    }
    else CHECK_INVARIANT(SHOULD_NOT_REACH, "Stack top must be either local or global when a name is entered")
}

double sym_Entry_for_Float_Var::get_Fvalue()                { return fvalue;    }

void sym_Entry_for_Float_Var::set_Fvalue(double num)        { fvalue = num;    }

/********************************* sym_Entry_for_Int_Var ******************************/

sym_Entry_for_Int_Var::sym_Entry_for_Int_Var(string s, int line)
{
    name = s;
    en_type = entity_Var;
    type = int_Val;
    start_offset = end_offset = 0;
    ivalue = 0;
    lineno = line;
    reg_desc_ptr = NULL;
     
    symtab_Stack_Top top = symtab_in_scope_P->get_Stack_Top();
   
    if (top == global)
    {
        undefined = false;
        sym_scope = is_Global;
    }
    else if (top == local)
    {
        undefined = true;
        sym_scope = is_Local;
    }
    else CHECK_INVARIANT(SHOULD_NOT_REACH, "Stack top must be either local or global when a name is entered")
}


int sym_Entry_for_Int_Var::get_Ivalue()                { return ivalue;    }

void sym_Entry_for_Int_Var::set_Ivalue(int num)        { ivalue = num;    }


/************************************* sym_List *************************/

sym_List::sym_List() 
{ 
     start_offset_of_first_sym = 0; 
     size_in_bytes = 0; 
}

void sym_List::set_Start_Offset_of_First_Sym (int n) { start_offset_of_first_sym = n; }

int sym_List::get_Start_Offset_of_First_Sym ()       { return start_offset_of_first_sym; }

void sym_List::set_Size (int n)                      { size_in_bytes; }

int sym_List::get_Size ()                            { return size_in_bytes; }



void sym_List::insert_Sym_Entry (sym_Entry_Ptr se_P)
{
    string name = se_P->get_Name();
    sym_list[name] = se_P;
}

bool sym_List::find_Name (string name)
{
    if (sym_list.count(name) == 1)
	return true;
    else return false;

}

sym_Entry_Ptr sym_List::get_Sym_Entry (string name)
{
    if (sym_list.count(name) == 1)
	return sym_list[name];
    else return NULL;

}

entity_Type sym_List::get_Entity_Type (string name)
{
    sym_Entry_Ptr se_P = sym_list[name];

    string mesg = "Variable " + name + "has not been entered in the symtab";

    CHECK_INVARIANT (se_P != NULL, mesg)

    return se_P->get_Entity_Type();
}

value_Type sym_List::get_Value_Type (string name)
{
    sym_Entry_Ptr se_P = sym_list[name];

    string mesg = "Variable " + name + "has not been entered in the symtab";

    CHECK_INVARIANT (se_P != NULL, mesg)

    return se_P->get_Value_Type();
}

int sym_List::get_Int_Val (string name)
{
    sym_Entry_Ptr se_P = sym_list[name];

    string mesg = "Variable " + name + "has not been entered in the symtab";

    CHECK_INVARIANT (se_P != NULL, mesg)

    return se_P->get_Ivalue();
}

double sym_List::get_Float_Val (string name)
{
    sym_Entry_Ptr se_P = sym_list[name];

    string mesg = "Variable " + name + "has not been entered in the symtab";

    CHECK_INVARIANT (se_P != NULL, mesg)

    return se_P->get_Fvalue();
}

sym_List& sym_List::operator=(sym_List& rhs)
{
    sym_list = rhs.sym_list;
    return *this;
}

/************************************* sym_Entry_for_Proc *************************/

sym_Entry_for_Proc::sym_Entry_for_Proc(string s, int line)
{
    name = s;
    en_type = entity_Proc;
    type = void_Val;
    lineno = line;
}

entity_Type sym_Entry_for_Proc::get_Entity_Type() { return entity_Proc; }

value_Type sym_Entry_for_Proc::get_Value_Type()   { return type; }

sym_Entry_for_Proc& sym_Entry_for_Proc::operator=(sym_Entry_for_Proc& rhs)
{
    name = rhs.name;
    en_type = rhs.en_type;
    type = rhs.type;
    sym_lp = rhs.sym_lp;
    lineno = rhs.lineno;

    return *this;
}

/* 
    The default procedures not applicable to all derived classes. Relevant 
    derived class must override it and provide meaningful body.
*/

void sym_Entry::set_Start_Offset(int num)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method set_Start_Offset is not relevant for this subclass of sym_Entry")
}

void sym_Entry::set_End_Offset(int num)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method set_End_Offset is not relevant for this subclass of sym_Entry")
}

void sym_Entry::set_Ivalue(int num)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method set_Value is not relevant for this subclass of sym_Entry")
}

void sym_Entry::set_Fvalue(double num)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method set_Value is not relevant for this subclass of sym_Entry")
}

int sym_Entry::get_Start_Offset()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method get_Start_Offset is not relevant for this subclass of sym_Entry")
}

int sym_Entry::get_End_Offset()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method get_End_Offset is not relevant for this subclass of sym_Entry")
}

int sym_Entry::get_Ivalue()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method get_Value is not relevant for this subclass of sym_Entry")
}
double sym_Entry::get_Fvalue()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method get_Value is not relevant for this subclass of sym_Entry")
}

void sym_Entry::set_Reg(reg_Desc_Ptr reg_desc_ptr)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "set_Reg cannot be called for this subclass of sym_Entry")
}

void sym_Entry::set_Value_of_Evaluation(eval_Result res)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method set_Value_of_Evaluation is not relevant for this subclass of sym_Entry")
}

eval_Result sym_Entry::get_Value_of_Evaluation()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "Method get_Value_of_Evaluation is not relevant for this subclass of sym_Entry")
}

reg_Desc_Ptr sym_Entry::get_Reg()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "set_Reg cannot be called for this subclass of sym_Entry")
}

sym_Scope sym_Entry::get_Sym_Scope()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Sym_Scope cannot be called for this subclass of sym_Entry")
}


/********************** evaluate ***********************/

void sym_List::set_Int_Val (string name, int value)
{
    sym_Entry_Ptr se_P = sym_list[name];

    string mesg = "Variable " + name + "has not been entered in the symtab";

    CHECK_INVARIANT (se_P != NULL, mesg)

    se_P->set_Ivalue(value);
}
void sym_List::set_Float_Val (string name, double value)
{
    sym_Entry_Ptr se_P = sym_list[name];

    string mesg = "Variable " + name + "has not been entered in the symtab";

    CHECK_INVARIANT (se_P != NULL, mesg)

    se_P->set_Fvalue(value);
}

/********************** compile ***********************/

void sym_List::assign_Offsets()
{
    map<string, sym_Entry_Ptr>::iterator i;

    for (i = sym_list.begin(); i != sym_list.end(); i++)
    {
        /* Check if the sym list entry is a variable and then assign offset to it */
        sym_Entry_Ptr se_P = i->second;

        if (se_P->get_Entity_Type() == entity_Var && !(se_P->exp_var_flag))
        {
            int size = get_Size_of_Value_Type(se_P->get_Value_Type());
            se_P->set_Start_Offset(size_in_bytes);
            size_in_bytes = size_in_bytes + size;
            se_P->set_End_Offset(size_in_bytes);
        }
    }

}

int get_Size_of_Value_Type(value_Type vt)
{
     switch(vt)
     {
         case int_Val: return 4; break;
		 case float_Val: return sizeof(double); break;
         case void_Val: CHECK_INVARIANT(SHOULD_NOT_REACH, "Attempt to seek size of type void") break;
         default: CHECK_INVARIANT(SHOULD_NOT_REACH, "Value type not supported") break;
     }
}
