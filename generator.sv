`include "transaction.sv"

class generator;
    // Declare transaction class
    rand transaction trans;
    
    // Repeat count and transaction counter
    int repeat_count, trans_num = 1;
    
    // Declare mailbox for communication
    mailbox gen2drv;
    event ended;
    
    // Constructor to initialize the mailbox
    function new(mailbox gen2drv);
        this.gen2drv = gen2drv;
    endfunction
    
    // Main task to run the generator sequence
    task main();
        $display("[Time: %0t] Generator: repeat_count = %0d", $time, repeat_count);
        
        repeat (repeat_count) begin
          repeat(3) begin
            // Valid header packets setup
            trans = new();
            trans.rx_data = 8'hAA; // LSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hAF; // MSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hAA; // LSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hAF; // MSB of valid header
            gen2drv.put(trans);
            // Payload: Generate 10 random payload bytes
            repeat (8) begin
                trans = new();
                if (!trans.randomize()) 
                    $fatal("[Time: %0t] Generator: trans randomization failed", $time);
                
                trans.display("[--Generator--]");
                gen2drv.put(trans);
                $display("[Time: %0t] Generator: Data sent to driver", $time);
            end//repeat 8
          end //repeat 3
            // Insert misalignment detection test sequence - 4 consecutive invalid frames
          repeat (4) begin
                trans = new();
                trans.rx_data = 8'hFF; // Invalid frame pattern
                gen2drv.put(trans);
                trans.display("[--Generator--] Sending Invalid Frame");
                $display("[Time: %0t] Generator: Sent Invalid Frame for Misalignment Test", $time);
                      repeat (11) begin
                trans = new();
                if (!trans.randomize()) 
                    $fatal("[Time: %0t] Generator: trans randomization failed", $time);
                
                trans.display("[--Generator--]");
                gen2drv.put(trans);
                $display("[Time: %0t] Generator: Data sent to driver", $time);
            end  //repeat 11
              
              
              
            end //repeat 4

          repeat(3) begin
            // Valid header packets setup
            trans = new();
            trans.rx_data = 8'h55; // LSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hBA; // MSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hAA; // LSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hAF; // MSB of valid header
            gen2drv.put(trans);
            // Payload: Generate 10 random payload bytes
            repeat (8) begin
                trans = new();
                if (!trans.randomize()) 
                    $fatal("[Time: %0t] Generator: trans randomization failed", $time);
                
                trans.display("[--Generator--]");
                gen2drv.put(trans);
                $display("[Time: %0t] Generator: Data sent to driver", $time);
            end//repeat 8
          end //repeat 3

        //ensure no mixing occures 
            // Invalid header packets setup
            repeat (4) begin
            trans = new();
            trans.rx_data = 8'hBA; // LSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'h55; // MSB of valid header
            gen2drv.put(trans);
           
            repeat (10) begin
                trans = new();
                if (!trans.randomize()) 
                    $fatal("[Time: %0t] Generator: trans randomization failed", $time);
                
                trans.display("[--Generator--]");
                gen2drv.put(trans);
                $display("[Time: %0t] Generator: Data sent to driver", $time);
            end//repeat 10
            end//repeat 4

          //repeat(3) begin
            // Valid header packets setup
            trans = new();
            trans.rx_data = 8'h55; // LSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hBA; // MSB of valid header
            gen2drv.put(trans);
            
            // Payload: Generate 10 random payload bytes
            repeat (10) begin
                trans = new();
                if (!trans.randomize()) 
                    $fatal("[Time: %0t] Generator: trans randomization failed", $time);
                
                trans.display("[--Generator--]");
                gen2drv.put(trans);
                $display("[Time: %0t] Generator: Data sent to driver", $time);
            end//repeat 10
                        trans = new();
            trans.rx_data = 8'hAA; // LSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hAF; // MSB of valid header
            gen2drv.put(trans);
            
            // Payload: Generate 10 random payload bytes
            repeat (10) begin
                trans = new();
                if (!trans.randomize()) 
                    $fatal("[Time: %0t] Generator: trans randomization failed", $time);
                
                trans.display("[--Generator--]");
                gen2drv.put(trans);
                $display("[Time: %0t] Generator: Data sent to driver", $time);
            end//repeat 10

                        trans = new();
            trans.rx_data = 8'h55; // LSB of valid header
            gen2drv.put(trans);
            
            trans = new();
            trans.rx_data = 8'hBA; // MSB of valid header
            gen2drv.put(trans);
            
            // Payload: Generate 10 random payload bytes
            repeat (10) begin
                trans = new();
                if (!trans.randomize()) 
                    $fatal("[Time: %0t] Generator: trans randomization failed", $time);
                
                trans.display("[--Generator--]");
                gen2drv.put(trans);
                $display("[Time: %0t] Generator: Data sent to driver", $time);
            end//repeat 10

          //end //repeat 3

            $display("[Time: %0t] Generator: trans_num = %0d", $time, trans_num);
            trans_num++;
            
            // Signal end of sequence if needed
            ->ended;
        end // repeat count
    endtask

endclass
