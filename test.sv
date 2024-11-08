`include "enviroment.sv"

program test(inf i_inf);
	
    // declare environment instance
    enviroment env;
	
    initial begin
        // create environment
        env = new (i_inf);
	
        // set the repeat count of generator as 6, i.e., generate 6 packets
        env.gen.repeat_count = 2000;
	
        // call run of env, it calls generator and driver main tasks
        env.run();
    end

endprogram

