interface inf (input logic clk, reset);
    
    // Signal declarations
   logic [3:0]  fr_byte_position; // byte position in a legal frame
   logic frame_detect;            // frame alignment indication
   logic  [7:0] rx_data;
   


    // Modport declarations for DUT (Device Under Test)
	modport DUT (input clk, reset, rx_data, output fr_byte_position, frame_detect);


  property valid_frame_1;
    @(posedge clk)
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_1);

  property valid_frame_2;
    @(posedge clk)
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_2);

  property valid_frame_3;
    @(posedge clk)
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_3);

  property valid_frame_4;
    @(posedge clk)
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_4);

  property valid_frame_5;
    @(posedge clk)
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_5);

  property valid_frame_6;
    @(posedge clk)
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_6);

  property valid_frame_7;
    @(posedge clk)
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_7);

  property valid_frame_8;
    @(posedge vinf.clk)
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_8);



endinterface




