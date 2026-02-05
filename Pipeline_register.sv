module pipeline_reg(input clk, rstn, in_valid, out_ready,
                    input [31:0] in_data,
                    output [31:0] out_data,
                    output in_ready, out_valid
                   );

	logic [31:0] data_reg;
  	logic valid_reg;

  	assign in_ready  = ~valid_reg || out_ready;
  	assign out_valid = valid_reg;
  	assign out_data  = data_reg;

  always@(posedge clk or negedge rstn)
  	begin
    	if(!rstn)
      		valid_reg <= 1'b0;
      
    	else begin
      		if(in_valid && in_ready)
            begin
        		data_reg <= in_data;
        		valid_reg <= 1'b1;
      		end
          
      		else if(out_ready && valid_reg)
	        	valid_reg <= 1'b0;
    	end
  	end
endmodule

module tb_pipeline_reg;
  
	logic clk, rstn, in_valid, out_ready;
  	logic [31:0] in_data;
	reg [31:0] out_data;
  	reg in_ready, out_valid;

  	pipeline_reg dut(.clk(clk), .rstn(rstn), .in_valid(in_valid), .out_ready(out_ready),
                   .in_data(in_data), .out_data(out_data),
                   .in_ready(in_ready), .out_valid(out_valid)
                  );

	always #5 clk = ~clk;

	initial begin
    	clk <= 0;
    	rstn <= 0;
    	in_valid <= 0;
    	in_data  <= 0;
    	out_ready <= 0;

    	#20 rstn = 1;

		@(posedge clk);
    	in_valid <= 1;
    	in_data  <= 32'hAAAA_AAAA;
    	out_ready <= 1;

    	@(posedge clk);
    	in_data  <= 32'hBBBB_BBBB;

    	@(posedge clk);
    	out_ready <= 0;

    	@(posedge clk);
    	out_ready <= 1;
    	in_valid  <= 0;
  	end

  	always @(posedge clk)
    begin
    	if(in_valid && in_ready)
          	$display($time," | INPUT TRANSFER : data = %0h",in_data);
      
      	if(out_valid && out_ready)
          	$display($time," | OUTPUT TRANSFER: data = %0h",out_data);
  	end
  
  	initial
     	#100 $finish;
  
  	property no_data_loss;
  		@(posedge clk)
  		disable iff (!rstn)
      
  		(in_valid && in_ready) |=> (out_valid && out_data == $past(in_data)) until (out_ready);
	endproperty

  	assert property (no_data_loss)
    else $error("Data loss detected!");
      
endmodule
