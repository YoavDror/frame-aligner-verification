class monitor_out;

  virtual inf vinf; // Create virtual interface handle
  mailbox mon2scbout; // Create mailbox handle
 
  // Constructor
  function new(virtual inf vinf, mailbox mon2scbout);
    this.vinf = vinf;
    this.mon2scbout = mon2scbout;
    // Instantiate the covergroup
    // byte_position_tracking_cg byte_position_tracking_cg_inst = new();
  endfunction
  
  // Samples the interface signal and sends the packet to scoreboard
  task main;
    forever begin
      transaction trans_out = new();
      @(negedge vinf.clk) begin
        trans_out.fr_byte_position = vinf.fr_byte_position;
        trans_out.frame_detect = vinf.frame_detect;
      //  byte_position_tracking_cg_inst.sample(); // Correctly call sample on the covergroup instance
      end
      mon2scbout.put(trans_out); // Send to scoreboard
    end
  endtask

 /* // Byte Position Tracking Coverage
  covergroup byte_position_tracking_cg;
    coverpoint vinf.fr_byte_position[3:0] {
      bins valid_byte_tracking = {[0:11]}; // Track positions 0 through 11
      ignore_bins invalid_positions = {[12:15]};  
    }
  endgroup */

endclass
