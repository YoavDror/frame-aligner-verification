class reference_model;

  // Internal counters for frame alignment model
  int na_byte_counter = 0;
  int frame_counter = 0;
  bit [7:0] previous_byte;
  bit update_fr_byte_position_clock_after = 0;
  bit update_frame_detect_clock_after = 0;

  // FSM Outputs
  bit frame_detect = 0;
  bit [3:0] fr_byte_position = 0;

  // FSM State
  typedef enum logic [1:0] {
    IDLE,
    H_LSB,
    H_MSB,
    PAYLOAD
  } state_t;

  state_t state = IDLE;

  // Process Frame Function (FSM logic)
  task process_frame(input bit [7:0] rx_data);
   // $display("[--State--]: %0d", state);
    case (state)
      IDLE: begin
        if (update_frame_detect_clock_after == 1) begin
          frame_detect = 0;
          update_frame_detect_clock_after = 0;
        end
        frame_counter = 0;
        na_byte_counter++;
        if (update_fr_byte_position_clock_after == 0) begin
        fr_byte_position = 0;  // Reset byte position in IDLE
        end
        else begin
          fr_byte_position = 1;
        end
        
        if (rx_data == 8'hAA || rx_data == 8'h55) begin
          state = H_LSB;
          previous_byte = rx_data;
        end else begin
          update_fr_byte_position_clock_after = 0 ;
          if (na_byte_counter == 47) begin
            na_byte_counter = 0;
            update_frame_detect_clock_after = 1;
          end
        end
      end

      H_LSB: begin
        fr_byte_position = 0;
        if ((rx_data == 8'hAF && previous_byte == 8'hAA) || 
            (rx_data == 8'hBA && previous_byte == 8'h55)) begin
          state = H_MSB;
          na_byte_counter = 0;
        end else begin
          if (rx_data == 8'hAA || previous_byte == 8'h55) begin
            state = H_LSB;
          end
          else begin
          update_fr_byte_position_clock_after = 1 ;
          state = IDLE;
          end
        end
      end

      H_MSB: begin
        fr_byte_position = 1;
        na_byte_counter = 0;
        frame_counter++;
        state = PAYLOAD;
      end

      PAYLOAD: begin
        if (frame_counter == 3) begin
          frame_detect = 1;
        end
        fr_byte_position++;
        if (fr_byte_position < 11) begin
          state = PAYLOAD;
        end else begin
          // Resetting or transitioning after payload is complete
          if (rx_data == 8'hAA || rx_data == 8'h55) begin
            state = H_LSB;
            previous_byte = rx_data;
          end else begin
            update_fr_byte_position_clock_after = 0 ;
            state = IDLE;
          end
        end
      end
    endcase
	
  endtask
endclass
