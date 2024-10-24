// testbench top is the top most file, in wich 

//DUT and verification enviorment are connected

`include "interface.sv"
`include "test.sv"

module top;

	//clock and reset signal declaraion
	bit clk;
	bit reset;
	
	//clocl geration
	always #5 clk = !clk;
	
	//reset genaration
	initial begin
		reset = 1;
		#15 reset = 0;
	end
	
	// interface instance in order to connect DUT and test bench
	inf i_inf(clk, reset);
	
	//testcase instance, interface handle is passed to test
	test t1(i_inf);
	
	//DUT instance, interface handle is passed to test
	frame_aligner DUT(i_inf);
	
endmodule