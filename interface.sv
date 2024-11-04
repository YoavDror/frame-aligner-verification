interface inf (input logic clk, reset);

  // Signal declarations
  logic [3:0] fr_byte_position; // Byte position in a legal frame
  logic frame_detect;           // Frame alignment indication
  logic [7:0] rx_data;

  // Modport declarations for DUT (Device Under Test)
  modport DUT (input clk, reset, rx_data, output fr_byte_position, frame_detect);

  // Byte Position Tracking Coverage Declaration
  //byte_position_tracking_cg byte_position_tracking_cg_inst = new();

  // Covergroup for byte position tracking
  covergroup byte_position_tracking_cg;
    coverpoint fr_byte_position[3:0] {
      bins valid_byte_tracking[] = {[0:11]}; // Track positions 0 through 11
      ignore_bins invalid_positions = {[12:15]};  
    }
  endgroup
  
  byte_position_tracking_cg byte_position_tracking_cg_inst;

  // Sampling block for the covergroup
  initial begin
	byte_position_tracking_cg_inst = new();
    forever @(posedge clk) begin
      byte_position_tracking_cg_inst.sample();
  
    end
  end
  
  
  
  // Sequence declarations for detecting headers
  sequence header_1;
    (rx_data == 8'hAA) ##1 (rx_data == 8'hAF);
  endsequence

  sequence header_2;
    (rx_data == 8'h55) ##1 (rx_data == 8'hBA);
  endsequence

// Properties for detecting valid frames
property valid_frame1;
  @(posedge clk)
  disable iff(reset)
 (fr_byte_position == 0) ##1 header_1 ##11 header_1 ##11 header_1 |=> (frame_detect == 1);
endproperty


property valid_frame2;
  @(posedge clk)
  disable iff(reset)
  (fr_byte_position == 0) ##1 header_1 ##11 header_1 ##11 header_2 |=> (frame_detect == 1);
endproperty

property valid_frame3;
  @(posedge clk)
  disable iff(reset)
  (fr_byte_position == 0) ##1 header_1 ##11 header_2 ##11 header_1 |=> (frame_detect == 1);
endproperty

property valid_frame4;
  @(posedge clk)
  disable iff(reset)
  (fr_byte_position == 0) ##1 header_1 ##11 header_2 ##11 header_2 |=> (frame_detect == 1);
endproperty

property valid_frame5;
  @(posedge clk)
  disable iff(reset)
  (fr_byte_position == 0) ##1 header_2 ##11 header_1 ##11 header_1 |=> (frame_detect == 1);
endproperty

property valid_frame6;
  @(posedge clk)
  disable iff(reset)
  (fr_byte_position == 0) ##1 header_2 ##11 header_1 ##11 header_2 |=> (frame_detect == 1);
endproperty

property valid_frame7;
  @(posedge clk)
  disable iff(reset)
  (fr_byte_position == 0) ##1 header_2 ##11 header_2 ##11 header_1 |=> (frame_detect == 1);
endproperty

property valid_frame8;
  @(posedge clk)
  disable iff(reset)
  (fr_byte_position == 0) ##1 header_2 ##11 header_2 ##11 header_2 |=> (frame_detect == 1);
endproperty 


  // Assertion and Coverage for the valid_frame1 property
assert property (valid_frame1)
  else $error("Error: frame_detect did not rise after three valid headers (header_1, header_1, header_1) in a row at time: %0t", $time);
valid_frame_1_inst: cover property (valid_frame1);

// Assertion and Coverage for the valid_frame2 property
assert property (valid_frame2)
  else $error("Error: frame_detect did not rise after three valid headers (header_1, header_1, header_2) in a row at time: %0t", $time);
valid_frame_2_inst: cover property (valid_frame2);

// Assertion and Coverage for the valid_frame3 property
assert property (valid_frame3)
  else $error("Error: frame_detect did not rise after three valid headers (header_1, header_2, header_1) in a row at time: %0t", $time);
valid_frame_3_inst: cover property (valid_frame3);

// Assertion and Coverage for the valid_frame4 property
assert property (valid_frame4)
  else $error("Error: frame_detect did not rise after three valid headers (header_1, header_2, header_2) in a row at time: %0t", $time);
valid_frame_4_inst: cover property (valid_frame4);

// Assertion and Coverage for the valid_frame5 property
assert property (valid_frame5)
  else $error("Error: frame_detect did not rise after three valid headers (header_2, header_1, header_1) in a row at time: %0t", $time);
valid_frame_5_inst: cover property (valid_frame5);

// Assertion and Coverage for the valid_frame6 property
assert property (valid_frame6)
  else $error("Error: frame_detect did not rise after three valid headers (header_2, header_1, header_2) in a row at time: %0t", $time);
valid_frame_6_inst: cover property (valid_frame6);

// Assertion and Coverage for the valid_frame7 property
assert property (valid_frame7)
  else $error("Error: frame_detect did not rise after three valid headers (header_2, header_2, header_1) in a row at time: %0t", $time);
valid_frame_7_inst: cover property (valid_frame7);

// Assertion and Coverage for the valid_frame8 property
assert property (valid_frame8)
  else $error("Error: frame_detect did not rise after three valid headers (header_2, header_2, header_2) in a row at time: %0t", $time);
valid_frame_8_inst: cover property (valid_frame8);


endinterface
