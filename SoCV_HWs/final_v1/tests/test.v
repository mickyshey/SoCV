module a (clk, z1, z2, z3, z4, z5);
input clk;
output z1, z2, z3, z4, z5;

reg x;
reg y;

assign z1 = x & y;
assign z2 = x & 1'b1;
assign z3 = x & 1'b0;
assign z4 = x | 1'b1;
assign z5 = x | 1'b0;

always @(posedge clk) begin
      x <= 1'b1;
      y <= 1'd1;
end
endmodule

