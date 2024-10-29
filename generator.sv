`include "frame_item.sv"
`include "transaction.sv"

class generator;
	// Declare transaction class
	transaction trans;

	// Repeat count to indicate number of items to generate
	int repeat_count;

	// Declare mailbox
	mailbox gen2drv;

	// Declare event to signal the end of transaction generation
	event ended;

	// Declare an instance of frame_item
	frame_item frame;

	// Constructor
	function new(mailbox gen2drv);
		// Get the mailbox handle from env, to share the transaction packet
		// between the generator and the driver
		this.gen2drv = gen2drv;
		this.frame = new(); // Initialize frame_item instance
	endfunction

	// Main task: generates `repeat_count` number of transaction packets and puts them into the mailbox
	task main();
		repeat (repeat_count) begin
			// Randomize frame_item
			if (!frame.randomize()) $fatal("Gen: frame randomization failed");

			// Display header and payload information
          $display("Generated frame:");
			$display("Header (LSB first): %h %h", frame.header_value[7:0], frame.header_value[15:8]);
			$display("Payload:");
			foreach (frame.payload[i]) begin
				$display("  Byte %0d: %h", i, frame.payload[i]);
			end

			// Send each byte of header_value in LSB-first order
			trans = new();
			trans.rx_data = frame.header_value[7:0]; // LSB of header
			gen2drv.put(trans);

			trans = new();
			trans.rx_data = frame.header_value[15:8]; // MSB of header
			gen2drv.put(trans);

			// Send each byte of the payload individually
			foreach (frame.payload[i]) begin
				trans = new();
				trans.rx_data = frame.payload[i];
				gen2drv.put(trans);
			end
		end
		-> ended;
	endtask
endclass
