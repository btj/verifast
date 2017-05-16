//The following predicates are auto generated 
/*@ 

predicate node (struct node *node; int count) = 
 node == 0 ? count == 0 : node->data |-> ?data &*& node->key |-> ?key &*& node->next |-> ?next &*& malloc_block_node(node)  &*& node(next, ?count1) &*& count == count1 + 1; 


@*/


struct node  {      char data;
   int key;   
   struct node *next;
};



//*******************************************************************************************************************************************
//THE FOLLOWING FUNCTION APPENDS TWO LISTS TOGETHER AND RETURN ONE POINTER AT THE END POINTING TO THE HEAD OF THE TWO LISTS APPENDED. THE USEER WILL HAVE TO MANUALLY INTERVENE (AFTER PRESSING AUTOFIX SIX TIMES) to change the logical variable count01 in THE loop's post-condition to a new fresh logical variable, e.g. ?count001. ALSO, DO NOT REMOVE THE LEAK COMMAND AT THE OF THE FUNCTION BECAUSE IT LEAKS THE HEAD2 POINTER WHICH IS ACTUALLY NULL.
//*******************************************************************************************************************************************


struct node* appendtwolists(struct node* head1, struct node* head2)
//@ requires true;
//@ ensures true;
{	
	if(head2 == NULL)
	{
		return head1;
			
	}
	else if(head1 == NULL)
	{
		head1 = head2;
		return head1;
	}
	else
	{
		struct node* current = head1;
		while (current != NULL)
		//@ requires true;
		//@ ensures true;
		{
		    if(current->next == NULL)
		    {
		    	current->next = head2;
		    	head2 = NULL;
		    	current = NULL;
		    }
		    else
		    {
			current = current->next;
			
		    }
		    //@ recursive_call();
		}
	//@leak node(head2,_);
	}
	return head1;
}
