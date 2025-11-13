// MyFSM Verification Excercise
//

module MyFSM(

        input clk,

        input x,

        output y);

    reg [1:0] state;

    assign y = state[1] & state[0] & x;

    always @ (negedge clk)

        case (state)

            2'b00: state <= x?2'b01:2'b00;

            2'b01: state <= x?2'b10:2'b00;

            2'b10: state <= x?2'b11:2'b00;

            2'b11: state <= 2'b00;

        endcase

endmodule