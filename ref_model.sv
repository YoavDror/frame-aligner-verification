class reference_model;

  // Internal counters for frame alignment model
  int na_byte_counter = 0;    // Non-aligned byte counter
  int frame_counter = 0;      // Frame counter for legal headers
  bit [7:0] previous_byte;    // To track the previous byte for MSB check

  // FSM Outputs
  bit frame_detect = 0;
  bit [3:0] fr_byte_position = 0;

  // FSM State
  typedef enum logic [2:0] {
    IDLE,
    H_LSB,
    H_MSB,
    PAYLOAD,
    ILLEGAL_BYTE
  } state_t;

  state_t state = IDLE;

  // Process Frame Function (FSM logic)
task process_frame(input bit [7:0] rx_data);
  $display("[--State--]: %0d", state);
    case (state)
      IDLE: begin
        if (rx_data == 8'hAA || rx_data == 8'h55) begin
          state = H_LSB;
          fr_byte_position = 0;
          na_byte_counter++;
          previous_byte = rx_data;
        end
        else begin
          state = ILLEGAL_BYTE;
          na_byte_counter++;
        end
      end

      H_LSB: begin
        if ((rx_data == 8'hAF && previous_byte == 8'hAA) || 
            (rx_data == 8'hBA && previous_byte == 8'h55)) begin
          state = H_MSB;
          na_byte_counter = 0;
          fr_byte_position = 1; // Start payload count at 1
        end
        else begin
          state = ILLEGAL_BYTE;
          na_byte_counter++;
          fr_byte_position = 0;
        end
      end

      H_MSB: begin
        state = PAYLOAD;
      end

      PAYLOAD: begin
        if (fr_byte_position < 11) begin
          fr_byte_position++;
        end
        else begin
          //fr_byte_position = 0; // Reset byte position for the next frame
          frame_counter++;
          if (frame_counter == 3) begin
            frame_detect = 1; // Set frame detect after three valid frames
          end
          state = IDLE; // Return to IDLE after processing a full frame
        end
      end

      ILLEGAL_BYTE: begin
        frame_counter = 0; // Ensure frame_counter is cleared
        if (rx_data == 8'hAA || rx_data == 8'h55) begin
          state = H_LSB;
          fr_byte_position = 0;
          na_byte_counter++;
          previous_byte = rx_data;
        end
        else begin
          na_byte_counter++;
          if (na_byte_counter == 47) begin
            frame_detect = 0; // Clear frame detect after 47 non-aligned bytes
           // frame_counter = 0; // Reset frame counter for the next attempt
            state = IDLE;
          end
        end
      end
    endcase
  endtask
endclass
