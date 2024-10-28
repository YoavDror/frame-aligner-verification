class transaction;

	//declare the transaction field
    rand bit [7:0] rx_data;
  		 bit [3:0] fr_byte_position;
 		 bit frame_detect;
		 
	// constraint rx_data_c {rx_data dist {8'hAF:=50, 8'hAA:=50};}
	
	function void display(string name);
	$display ("---------------------------");
	$display("- %s ", name);
	$display ("---------------------------");
    $display("- rx_data = %h", rx_data);
    $display("- fr_byte_position = %d, frame_detect = %d ", fr_byte_position, frame_detect);
	$display ("---------------------------");
	endfunction

endclass

