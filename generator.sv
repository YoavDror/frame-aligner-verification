`include "transaction.sv"
class generator;
	// declare transaction class
	transaction trans;
	
	//repeat count to indicate number of items to generate
	int repeat_count;
	
	// declare mailbox
	mailbox gen2drv;
	
	//declare event , to in the end of transaction generation
	event ended;
	
	//constructer
	function new(mailbox gen2drv);
		//get the mailbox handle fron env, in order to share the transaction packet
		//between the gererator and the driver the same mailbox is shared between both.
		this.gen2drv = gen2drv;
	endfunction
	
	//main task, gerates (creat randomized) the repeat_count
	//number of transaction packets and puts them into the mailbox
	task main();
	 repeat(repeat_count) begin
		trans = new();
		if ( !trans.randomize() ) $fatal("Gen: trans randomization failied");
		//trans.display("[ --Generator-- ]");
		gen2drv.put(trans);
	 end
	 -> ended;
	endtask
	
endclass
