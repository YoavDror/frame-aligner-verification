class reference_model;

  // Internal counters for frame alignment model
  int na_byte_counter = 0;
  int frame_counter = 0;
  bit [7:0] previous_byte;

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
    $display("[--State--]: %0d", state);
    case (state)
      IDLE: begin
        frame_counter = 0;
        na_byte_counter++;
        fr_byte_position = 0;  // Reset byte position in IDLE
        if (rx_data == 8'hAA || rx_data == 8'h55) begin
          state = H_LSB;
          previous_byte = rx_data;
        end else if (na_byte_counter == 47) begin
          frame_detect = 0;
          na_byte_counter = 0;
        end
      end

      H_LSB: begin
        fr_byte_position = 0;
        if ((rx_data == 8'hAF && previous_byte == 8'hAA) || 
            (rx_data == 8'hBA && previous_byte == 8'h55)) begin
          state = H_MSB;
          na_byte_counter = 0;
        end else begin
          state = IDLE;
        end
      end

      H_MSB: begin
        fr_byte_position = 1;
        na_byte_counter = 0;
        frame_counter++;
        if (frame_counter == 3) begin
          frame_detect = 1;
        end
        state = PAYLOAD;
      end

      PAYLOAD: begin
        fr_byte_position++;
        if (fr_byte_position < 11) begin
          // Stay in PAYLOAD state until payload bytes complete
        end else begin
          // Transition after payload is complete
          if (rx_data == 8'hAA || rx_data == 8'h55) begin
            state = H_LSB;
            previous_byte = rx_data;
          end else begin
            state = IDLE;
          end
        end
      end
    endcase
  endtask
endclass
