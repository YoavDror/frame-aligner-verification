class driver;
	
	//count the number of transations
	int num_transactions;
	
	//creat mailbox handle
	mailbox gen2drv;
  
   // Declare virtual interface
    virtual inf vinf;
	
	//constructor
	function new (virtual inf vinf, mailbox gen2drv);
		//get the interface
		this.vinf = vinf;
		//get the mailbox handke fron env
		this.gen2drv = gen2drv;
	endfunction

	//Reset task, Reset the inteface signals to default/initial values
	task reset;
	wait(vinf.reset);
	$display("[ --DRIVER-- ] ----- Reset Started -----");
	vinf.rx_data <= 8'b0;
    wait(!vinf.reset);
	$display("[ --DRIVER-- ] ----- Reset Ended  -----");
	endtask
	
	
	//drives the transaction items into interface signals 
	task main;
	forever begin
	transaction trans;
	gen2drv.get(trans);
    @(posedge vinf.clk);
    vinf.rx_data <= trans.rx_data;
	//trans.display("[ --Driver-- ]");
	num_transactions++;
	end
	endtask

endclass
