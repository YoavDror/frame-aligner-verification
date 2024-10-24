class scoreboard;

  // Mailboxes for transactions
  mailbox mon2scbin, mon2scbout;
  
  // Transaction counters
  int num_transactions = 0;
  int error_counter = 0;

  // Internal counters for frame align model
  int na_byte_counter = 0;    // Non-aligned byte counter
  int frame_counter = 0;      // Frame counter for legal headers
  int payload_byte_count = 0; // Counter for bytes in the payload
  bit [7:0] previous_byte;    // To track the previous byte (for MSB check)

  // FSM Outputs
  bit frame_detect = 0;
  bit [3:0] fr_byte_position = 0;

  // FSM State
  typedef enum logic [2:0] {
    IDLE,
    NA_BYTE_COUNT,
    MISALIGNED,
    LSB,
    MSB,
    PAYLOAD,
    ALIGNED
  } state_t;

  state_t frame_state = IDLE;

  // Constructor
  function new(mailbox mon2scbin, mailbox mon2scbout);
    this.mon2scbin = mon2scbin;
    this.mon2scbout = mon2scbout;
  endfunction

  // Process Frame Function (FSM logic inside the scoreboard)
  task process_frame(input bit [7:0] data_byte);
    case (frame_state)
      IDLE: begin
        if (data_byte == 8'hAA || data_byte == 8'h55) begin  // Valid LSB
          frame_state = LSB;  // Move to LSB state
          previous_byte = data_byte;  // Store LSB for next cycle
        end else begin
          frame_state = NA_BYTE_COUNT;  // Move to NA_BYTE_COUNT state
          na_byte_counter = 0;  // Reset non-aligned byte counter
        end
      end

      NA_BYTE_COUNT: begin
        na_byte_counter++;
        if (na_byte_counter == 47) begin
          frame_state = MISALIGNED;
          frame_detect = 0;  // Misaligned, set frame_detect = 0
		  frame_counter = 0;
        end else begin
          frame_state = IDLE;  // Return to IDLE if not 47 bytes
        end
      end

      MISALIGNED: begin
        if (data_byte == 8'hAA || data_byte == 8'h55) begin
          frame_state = LSB;  // Start realignment on valid LSB
          na_byte_counter = 0;  // Reset non-aligned byte counter
          previous_byte = data_byte;  // Store LSB
        end
      end

      LSB: begin
        fr_byte_position = 0;
        if ((previous_byte == 8'hAA && data_byte == 8'hAF) || 
            (previous_byte == 8'h55 && data_byte == 8'hBA)) begin
          frame_state = MSB;  // Move to MSB state
          frame_counter++;    // Increment frame counter for valid frame
        end else begin
          frame_state = NA_BYTE_COUNT;  // Return to non-aligned count on invalid MSB
          na_byte_counter = 0;  // Reset counter
        end
      end

      MSB: begin
        frame_state = PAYLOAD;  // Move to PAYLOAD state
        fr_byte_position = 1;   // Start payload byte count
        payload_byte_count = 0; // Reset payload byte counter
      end

      PAYLOAD: begin
        fr_byte_position++;
        payload_byte_count++;

        if (fr_byte_position == 11) begin  // After processing full payload (10 bytes)
          if (frame_counter == 3) begin
            frame_state = ALIGNED;
            frame_detect = 1;  // Frame detect = 1 after 3 valid frames
          end else begin
            frame_state = IDLE;  // Go back to IDLE after payload
            frame_detect = 0;    // Reset frame detect
          end
        end
      end

      ALIGNED: begin
        frame_detect = 1;  // Stay in aligned state
        frame_state = IDLE;  // Go back to IDLE for next frame
      end
    endcase
  endtask
  
  // Main scoreboard comparison logic
  task main;
    transaction trans_in, trans_out;

    forever begin
      // Get input transaction (from monitor)
      mon2scbin.get(trans_in);
      
      // Get output transaction (from DUT)
      mon2scbout.get(trans_out);

      // Pass the incoming data (trans_in.rx_data) through the FSM inside the scoreboard
      process_frame(trans_in.rx_data);

      // Compare the actual vs reference outputs
      if ((trans_out.frame_detect == frame_detect) && 
          (trans_out.fr_byte_position == fr_byte_position)) begin
        $display("[--Scoreboard--] Result as Expected");
        $display("Frame Detect: %0b, Byte Position: %0d", trans_out.frame_detect, trans_out.fr_byte_position);
      end else begin
        $display("[--Scoreboard--] Mismatch detected!");
        $display("Expected Frame Detect: %0b, Actual Frame Detect: %0b", frame_detect, trans_out.frame_detect);
        $display("Expected Byte Position: %0d, Actual Byte Position: %0d", fr_byte_position, trans_out.fr_byte_position);
        error_counter++;
      end

      num_transactions++;
      
      if (num_transactions == 100) begin
        $display("[--Scoreboard--] Total Errors: %0d", error_counter);
      end
    end
  endtask
endclass
