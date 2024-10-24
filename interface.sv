interface inf (input logic clk, reset);
    
    // Signal declarations
   logic [3:0]  fr_byte_position; // byte position in a legal frame
   logic frame_detect;            // frame alignment indication
   logic  [7:0] rx_data;
   


    // Modport declarations for DUT (Device Under Test)
	modport DUT (input clk, reset, rx_data, output fr_byte_position, frame_detect);

endinterface

