
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

void sym_Entry_for_Var::print_Sym_Entry_Details(ostream * sym_fp)
{

    string k_mesg = "The entity type of name " + name + " should have been variable";
    CHECK_INVARIANT (en_type == entity_Var, k_mesg)
    const string en_type_name = "VAR";
    string type_name;
    string t_mesg = "The type of entity_Var " + name + " should have been int_Val or float_Val";
    CHECK_INVARIANT (type == int_Val || type == float_Val, t_mesg)
    if(type == int_Val)
		type_name = "INT";
	else
		type_name = "FLOAT"; 

    if (!exp_var_flag)
    {
        *sym_fp << " Name: " << name << " Type: " << type_name << " Entity Type: " << en_type_name;
        if (start_offset == end_offset)
            *sym_fp << " (No offset assigned yet)\n"; 
        else
            *sym_fp << " Start Offset: " << start_offset << " End Offset: " << end_offset << "\n"; 
    }
}

void sym_List::print_Sym_Node_List(ostream * sym_fp)
{ 
    map<string, sym_Entry_Ptr>::iterator i;

    for (i = sym_list.begin(); i != sym_list.end(); i++)
        i->second->print_Sym_Entry_Details(sym_fp); 
}

void sym_Entry_for_Proc::print_Sym_Entry_Details(ostream * sym_fp)
{

    string mesg = "Wrong value of entity type field for a symbol entry representing a procedure " + name;
    CHECK_INVARIANT (en_type == entity_Proc, mesg)
    const string en_type_name = "FUNC";
    string type_name;
	if(type == int_Val) 
		type_name="INT";
	else if(type == float_Val)
		type_name = "FLOAT";
	else type_name = "VOID";

    *sym_fp << " Name: " << name << " Type: " << type_name << " Entity Type: " << en_type_name << "\n"; 
}

void sym_List::print_Sym_Node_List_for_Evaluation(ostream * sym_fp)
{ 
    map<string, sym_Entry_Ptr>::iterator i;

    for (i = sym_list.begin(); i != sym_list.end(); i++)
    {
        /* Check if the sym list entry is a name and then print it */
        sym_Entry_Ptr se_P = i->second;

        if (se_P->get_Entity_Type() == entity_Var)
            se_P->print_Sym_Entry_Eval_Details(sym_fp); 
    }
}

void sym_Entry_for_Var::print_Sym_Entry_Eval_Details(ostream * sym_fp)
{
    if (!exp_var_flag)
    {
        string k_mesg = "The entity type of name " + name + " should have been variable";
        CHECK_INVARIANT (en_type == entity_Var, k_mesg)
        const string en_type_name = "VAR";
        string type_name;
        string t_mesg = "The type of entity_Var " + name + " should have been int_Val or float_Val";
        CHECK_INVARIANT (type == int_Val || type == float_Val, t_mesg)
     	stringstream ss;
        if(type == int_Val) {
    		type_name = "INT";
    		if (undefined)
            	ss << "Undefined";
        	else
            	ss << ivalue;
    		 *sym_fp << " Name: " << name << " Value " << ss.str() << "\n";
    	}
       else {
                ss.setf(std::ios::fixed);
                ss.precision(6);
    			type_name = "FLOAT"; 
    	    	if (undefined)
        	    	ss << "Undefined";
        		else
        	    	ss << fvalue;
    			 *sym_fp << " Name: " << name << " Value " << ss.str() << "\n";
    		}
    }
}

/**************************** functions for generating assembly ******************/

void sym_List::print_Sym_for_Assembly(ostream * sym_fp)
{ 
    map<string, sym_Entry_Ptr>::iterator i;

    for (i = sym_list.begin(); i != sym_list.end(); i++)
    {
        /* Check if the sym list entry is a name and then print it */
        sym_Entry_Ptr se_P = i->second;

        if (se_P->get_Entity_Type() == entity_Var)
            se_P->print_Sym_for_Assembly(sym_fp); 
    }
}

void sym_Entry_for_Var::print_Sym_for_Assembly(ostream * sym_fp)
{

	string k_mesg = "The entity type of name " + name + " should have been variable";
    CHECK_INVARIANT (en_type == entity_Var, k_mesg)
    const string en_type_name = "VAR";
    string type_name;
    string t_mesg = "The type of entity_Var " + name + " should have been int_Val or float_Val";
    CHECK_INVARIANT (type == int_Val || type == float_Val, t_mesg)
    if(type == int_Val)
		type_name = "INT";
	else
		type_name = "FLOAT"; 

    CHECK_INVARIANT(sym_scope == is_Global, "Global scope value expected")
    *sym_fp << name << ":\t.word 0\n";
}

void sym_Entry::print_Sym_for_Assembly(ostream * sym_fp)
{
    CHECK_INVARIANT (SHOULD_NOT_REACH, "Symbol does not qualify as global data in assembly output")
}
