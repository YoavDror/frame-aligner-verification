class monitor_out;

  virtual inf vinf; // Create virtual interface handle
  mailbox mon2scbout; // Create mailbox handle
  
  // Constructor
  function new(virtual inf vinf, mailbox mon2scbout);
    this.vinf = vinf;
    this.mon2scbout = mon2scbout;
  endfunction
  
  // Samples the interface signal and sends the packet to scoreboard
  task main;
    forever begin
      transaction trans_out = new();
      @(negedge vinf.clk) begin
        trans_out.rx_data = vinf.rx_data;
        trans_out.fr_byte_position = vinf.fr_byte_position;
        trans_out.frame_detect = vinf.frame_detect;
      end
      mon2scbout.put(trans_out); // Send to scoreboard
    end
  endtask

  // Byte Position Tracking Coverage
  covergroup byte_position_tracking_cg @(negedge vinf.clk);
    coverpoint vinf.fr_byte_position[3:0] {
      bins valid_byte_tracking = {[0:11]}; // Track positions 0 through 11
    }
  endgroup

  // Instantiate the covergroup
  byte_position_tracking_cg byte_position_tracking_cg_inst = new();

  // Sequence-based coverage for Legal Frame Detection

  property valid_frame_1;
    @(posedge vinf.clk)
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_1);

  property valid_frame_2;
    @(posedge vinf.clk)
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_2);

  property valid_frame_3;
    @(posedge vinf.clk)
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_3);

  property valid_frame_4;
    @(posedge vinf.clk)
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_4);

  property valid_frame_5;
    @(posedge vinf.clk)
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_5);

  property valid_frame_6;
    @(posedge vinf.clk)
      (vinf.rx_data == 8'hBA) ##1 (vinf.rx_data == 8'h55) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF}) ##
      (vinf.rx_data == 8'hAF) ##1 (vinf.rx_data == 8'hAA) ##1 [*10](vinf.rx_data inside {8'h00:8'hFF});
  endproperty
  cover property (valid_frame_6);

  property valid_frame_7;
    @(posedge vinf.clk)
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

endclass
