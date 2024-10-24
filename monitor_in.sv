class monitor_in;
  
  virtual inf vinf; //create virtual interface handle
  mailbox mon2scbin; //create mailbox handle
  
  // Constructor
  function new(virtual inf vinf, mailbox mon2scbin);
    this.vinf = vinf;
    this.mon2scbin = mon2scbin;
  endfunction
  
  // Samples the interface signal and sends the packet to scoreboard
  task main;
    forever begin
      transaction trans_in = new();
      @(posedge vinf.clk); // Sample at posedge
      trans_in.rx_data <= vinf.rx_data;
  //    trans_in.display("[ --Monitor_in-- ]");
  
  /*Write a condition to pass only valid headers.. and find a way to count in the corebord 10 bytes insted of passing them one by one*/
      mon2scbin.put(trans_in); // Send to scoreboard
    end
  endtask
endclass
