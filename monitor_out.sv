class monitor_out;
  
  virtual inf vinf; //create virtual interface handle
  mailbox mon2scbout; //create mailbox handle
  
  // Constructor
  function new(virtual inf vinf, mailbox mon2scbout);
    this.vinf = vinf;
    this.mon2scbout = mon2scbout;
  endfunction
  
  // Samples the interface signal and sends the packet to scoreboard
  task main;
    forever begin
      transaction trans_out = new();
      @(negedge vinf.clk) begin // Wait for ALU output (after negedge)
	  trans_out.fr_byte_position = vinf.fr_byte_position;
      trans_out.frame_detect = vinf.frame_detect;
      //trans_out.display("[ --Monitor_out-- ]");
      end
      mon2scbout.put(trans_out); // Send to scoreboard
    end
  endtask
endclass
