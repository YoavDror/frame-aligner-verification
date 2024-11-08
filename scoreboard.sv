`include "reference_model.sv"

class scoreboard;

  // Mailboxes for transactions
  mailbox mon2scbin, mon2scbout;
  
  // Transaction counters
  int num_transactions = 0;
  int error_counter = 0;

  // Reference Model Instance
  reference_model ref_model;

  // Constructor
  function new(mailbox mon2scbin, mailbox mon2scbout);
    this.mon2scbin = mon2scbin;
    this.mon2scbout = mon2scbout;
    ref_model = new(); // Instantiate the reference model
  endfunction

  // Main scoreboard comparison logic
  task main;
    transaction trans_in, trans_out;

    forever begin
      // Get input transaction (from monitor)
      mon2scbin.get(trans_in);
      
      // Get output transaction (from DUT)
      mon2scbout.get(trans_out);

      // Process the incoming data with the reference model's FSM
      ref_model.process_frame(trans_in.rx_data);
      
      // Compare the actual vs expected outputs
      if ((trans_out.frame_detect == ref_model.frame_detect) && 
          (trans_out.fr_byte_position == ref_model.fr_byte_position)) begin
        //$display("[--Scoreboard--] Result as Expected");
       // $display("Frame Detect: %0b, Byte Position: %0d", trans_out.frame_detect, trans_out.fr_byte_position);
      end else begin
        $display("[--Scoreboard--] Mismatch detected!");
        $display("Current time is: %0t", $time);
        $display("Expected Frame Detect: %0b, Actual Frame Detect: %0b", ref_model.frame_detect, trans_out.frame_detect);
        $display("Expected Byte Position: %0d, Actual Byte Position: %0d", ref_model.fr_byte_position, trans_out.fr_byte_position);
        error_counter++;
      end

      num_transactions++;
      
      if (num_transactions == 2000) begin
        $display("[--Scoreboard--] Total Errors: %0d/%0d", error_counter,num_transactions);
      end
    end
  endtask
endclass
