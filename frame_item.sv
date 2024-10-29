class frame_item;
  typedef enum bit [1:0] {HEAD_1, HEAD_2, ILLEGAL} header_type_t;

  rand header_type_t header;
  rand byte payload[];
  logic [15:0] header_value;

  function new();
    this.payload = new[0]; // Initialize dynamic array
  endfunction

  // Constraint to give the payload a non-zero length and random values
  constraint payload_c {
    payload.size() inside {[9:10]}; // Set payload size in range 9 - 10 bytes
    foreach (payload[i]) payload[i] inside {[8'h00:8'hFF]}; // Allow random values for each byte
  }

  constraint header_distribution {
    header dist {HEAD_1 := 35, HEAD_2 := 35, ILLEGAL := 30};
  }

  function void post_randomize();
    case (header)
      HEAD_1: header_value = 16'hAFAA;
      HEAD_2: header_value = 16'hBA55;
      ILLEGAL: header_value = $urandom_range(16'h0000, 16'hFFFF);
    endcase
  endfunction
endclass
