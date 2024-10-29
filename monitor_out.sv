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
      bins valid_byte_tracking = {4'h1 => 4'h2 => 4'h3 => 4'h4 => 4'h5 => 4'h6 => 4'h7 => 4'h8 => 4'h9 => 4'ha => 4'hb}; // Track positions 0 through 11
    }
  endgroup

  // Legal Frame Detection Coverage
covergroup Legal_frame_detection_cg @(negedge vinf.clk);
  coverpoint vinf.rx_data {
    // Sequences with three consecutive valid frames using different combinations of headers and payloads
    bins valid_frame_1[] = {8'hAF => 8'hAA => 10*[8'h00:8'hFF] => 8'hAF => 8'hAA => 10*[8'h00:8'hFF] => 8'hAF => 8'hAA => 10*[8'h00:8'hFF]};
    bins valid_frame_2[] = {8'hBA => 8'h55 => 10*[8'h00:8'hFF] => 8'hBA => 8'h55 => 10*[8'h00:8'hFF] => 8'hBA => 8'h55 => 10*[8'h00:8'hFF]};
    bins valid_frame_3[] = {8'hAF => 8'hAA => 10*[8'h00:8'hFF] => 8'hBA => 8'h55 => 10*[8'h00:8'hFF] => 8'hAF => 8'hAA => 10*[8'h00:8'hFF]};
    bins valid_frame_4[] = {8'hBA => 8'h55 => 10*[8'h00:8'hFF] => 8'hAF => 8'hAA => 10*[8'h00:8'hFF] => 8'hBA => 8'h55 => 10*[8'h00:8'hFF]};
    bins valid_frame_5[] = {8'hAF => 8'hAA => 10*[8'h00:8'hFF] => 8'hBA => 8'h55 => 10*[8'h00:8'hFF] => 8'hBA => 8'h55 => 10*[8'h00:8'hFF]};
    bins valid_frame_6[] = {8'hBA => 8'h55 => 10*[8'h00:8'hFF] => 8'hAF => 8'hAA => 10*[8'h00:8'hFF] => 8'hAF => 8'hAA => 10*[8'h00:8'hFF]};
    bins valid_frame_7[] = {8'hAF => 8'hAA => 10*[8'h00:8'hFF] => 8'hAF => 8'hAA => 10*[8'h00:8'hFF] => 8'hBA => 8'h55 => 10*[8'h00:8'hFF]};
    bins valid_frame_8[] = {8'hBA => 8'h55 => 10*[8'h00:8'hFF] => 8'hBA => 8'h55 => 10*[8'h00:8'hFF] => 8'hAF => 8'hAA => 10*[8'h00:8'hFF]};
  }
endgroup

  byte_position_tracking_cg byte_position_tracking_cg_inst = new;
  Legal_frame_detection_cg Legal_frame_detection_cg_inst = new;

endclass
