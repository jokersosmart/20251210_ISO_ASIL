/**
 * @file supply_sequencer.v
 * @brief Power Supply Sequencing and Safe State Entry
 *
 * Implements power sequencing and safe state entry logic.
 * Coordinates multi-stage power supply ramp-up and safe state transitions.
 *
 * Design Specifications (T017):
 *  - Support 3-stage power ramp: 1V → 2V → 3.3V
 *  - Configurable delay per stage
 *  - Detects brownout and triggers safe state entry
 *  - Manages system reset sequencing
 */

`timescale 1ns / 1ps

module supply_sequencer (
    input  wire        clk,              // System clock (400MHz)
    input  wire        reset_n,          // Global reset
    input  wire        vdd_fault,        // VDD fault from monitor
    input  wire        sys_shutdown_req, // Software shutdown request
    
    // Configuration inputs
    input  wire [15:0] delay_stage1,     // Stage 1 delay (1V hold time)
    input  wire [15:0] delay_stage2,     // Stage 2 delay (2V hold time)
    input  wire [15:0] delay_stage3,     // Stage 3 delay (3.3V stable time)
    
    // Control outputs
    output reg         safe_state_en,    // Enter safe state (1 = safe state active)
    output reg         supply_enable,    // Master supply enable
    output reg  [1:0]  power_stage,      // Current power stage (00=off, 01=1V, 10=2V, 11=3.3V)
    
    // Status outputs
    output wire [3:0]  fsm_state,        // FSM state (debug)
    output wire        supply_stable     // All supplies stable
);

// ============================================================================
// FSM State Definitions
// ============================================================================

localparam [3:0] STATE_POWEROFF = 4'b0000;
localparam [3:0] STATE_STAGE1_RAMP = 4'b0001;    // 1V ramp
localparam [3:0] STATE_STAGE1_SETTLE = 4'b0010;  // Wait for 1V settle
localparam [3:0] STATE_STAGE2_RAMP = 4'b0011;    // 2V ramp
localparam [3:0] STATE_STAGE2_SETTLE = 4'b0100;  // Wait for 2V settle
localparam [3:0] STATE_STAGE3_RAMP = 4'b0101;    // 3.3V ramp
localparam [3:0] STATE_STAGE3_SETTLE = 4'b0110;  // Wait for 3.3V settle (final)
localparam [3:0] STATE_RUNNING = 4'b0111;        // Normal operation
localparam [3:0] STATE_SAFE_STATE_ENTRY = 4'b1000; // Entering safe state
localparam [3:0] STATE_SAFE_STATE = 4'b1001;     // Safe state active
localparam [3:0] STATE_SHUTDOWN = 4'b1111;       // Complete shutdown

// ============================================================================
// State Machine Variables
// ============================================================================

reg [3:0] current_state, next_state;
reg [15:0] delay_counter;
reg supply_stable_r;

// ============================================================================
// FSM Main Logic
// ============================================================================

always @(*) begin
    next_state = current_state;
    safe_state_en = 1'b0;
    supply_enable = 1'b0;
    power_stage = 2'b00;  // Default: off
    supply_stable_r = 1'b0;
    
    case (current_state)
        STATE_POWEROFF: begin
            // System powered off
            safe_state_en = 1'b0;
            supply_enable = 1'b0;
            power_stage = 2'b00;
            
            if (!sys_shutdown_req && !reset_n) begin
                // Start power-on sequence
                next_state = STATE_STAGE1_RAMP;
                supply_enable = 1'b1;
            end
        end
        
        STATE_STAGE1_RAMP: begin
            // Ramping to 1V
            supply_enable = 1'b1;
            power_stage = 2'b01;
            
            if (delay_counter >= delay_stage1) begin
                next_state = STATE_STAGE1_SETTLE;
            end
        end
        
        STATE_STAGE1_SETTLE: begin
            // Waiting for 1V to settle
            supply_enable = 1'b1;
            power_stage = 2'b01;
            
            next_state = STATE_STAGE2_RAMP;
        end
        
        STATE_STAGE2_RAMP: begin
            // Ramping to 2V
            supply_enable = 1'b1;
            power_stage = 2'b10;
            
            if (delay_counter >= delay_stage2) begin
                next_state = STATE_STAGE2_SETTLE;
            end
        end
        
        STATE_STAGE2_SETTLE: begin
            // Waiting for 2V to settle
            supply_enable = 1'b1;
            power_stage = 2'b10;
            
            next_state = STATE_STAGE3_RAMP;
        end
        
        STATE_STAGE3_RAMP: begin
            // Ramping to 3.3V (final stage)
            supply_enable = 1'b1;
            power_stage = 2'b11;
            
            if (delay_counter >= delay_stage3) begin
                next_state = STATE_STAGE3_SETTLE;
            end
        end
        
        STATE_STAGE3_SETTLE: begin
            // Waiting for 3.3V to stabilize
            supply_enable = 1'b1;
            power_stage = 2'b11;
            supply_stable_r = 1'b1;
            
            if (!vdd_fault) begin
                // Supply is stable and no fault
                next_state = STATE_RUNNING;
            end
        end
        
        STATE_RUNNING: begin
            // Normal operation - all supplies stable
            supply_enable = 1'b1;
            power_stage = 2'b11;
            supply_stable_r = 1'b1;
            
            if (vdd_fault) begin
                // Fault detected - enter safe state
                next_state = STATE_SAFE_STATE_ENTRY;
            end else if (sys_shutdown_req) begin
                // Software shutdown requested
                next_state = STATE_SHUTDOWN;
            end
        end
        
        STATE_SAFE_STATE_ENTRY: begin
            // Transitioning to safe state
            safe_state_en = 1'b1;
            supply_enable = 1'b1;
            power_stage = 2'b11;
            
            // After 1 clock, move to safe state
            next_state = STATE_SAFE_STATE;
        end
        
        STATE_SAFE_STATE: begin
            // Safe state active - waiting for recovery
            safe_state_en = 1'b1;
            supply_enable = 1'b1;
            power_stage = 2'b11;
            
            if (!vdd_fault) begin
                // Fault cleared - attempt recovery
                next_state = STATE_RUNNING;
            end
        end
        
        STATE_SHUTDOWN: begin
            // Complete shutdown
            safe_state_en = 1'b0;
            supply_enable = 1'b0;
            power_stage = 2'b00;
            
            // Stay in shutdown until manual reset
        end
        
        default: begin
            next_state = STATE_POWEROFF;
        end
    endcase
end

// ============================================================================
// Sequential Logic - State and Delay Counter
// ============================================================================

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        current_state <= STATE_POWEROFF;
        delay_counter <= 16'd0;
    end else begin
        current_state <= next_state;
        
        // Delay counter logic
        case (next_state)
            STATE_STAGE1_RAMP, STATE_STAGE2_RAMP, STATE_STAGE3_RAMP: begin
                // Count delays for each stage
                if (delay_counter < 16'hFFFF) begin
                    delay_counter <= delay_counter + 1'b1;
                end
            end
            
            STATE_STAGE1_SETTLE, STATE_STAGE2_SETTLE, STATE_STAGE3_SETTLE,
            STATE_SAFE_STATE_ENTRY: begin
                // Reset counter when moving to settle stages
                delay_counter <= 16'd0;
            end
            
            default: begin
                delay_counter <= 16'd0;
            end
        endcase
    end
end

// ============================================================================
// Output Registers
// ============================================================================

always @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        safe_state_en <= 1'b0;
        supply_enable <= 1'b0;
        power_stage <= 2'b00;
    end else begin
        // Combinational logic already computed above
        // Just register the outputs from next_state logic
    end
end

// ============================================================================
// Output Assignment
// ============================================================================

assign fsm_state = current_state;
assign supply_stable = supply_stable_r;

// ============================================================================
// Timing Specifications
// ============================================================================

// Power-up sequence timing (example values, configurable):
//  - Stage 1 (1V): 10ms hold time
//  - Stage 2 (2V): 10ms hold time
//  - Stage 3 (3.3V): 50ms stabilization time
//  - Total startup: ~70ms

// At 400MHz, this translates to:
//  - Stage 1: 10ms × 400MHz = 4,000,000 cycles
//  - Stage 2: 10ms × 400MHz = 4,000,000 cycles
//  - Stage 3: 50ms × 400MHz = 20,000,000 cycles
//  (Note: Using 16-bit counter for demo, actual implementation uses wider counters)

// ============================================================================
// Safe State Entry Timing
// ============================================================================

// Per SysReq-002 requirement: Safe state entry < 10ms
// This implementation transitions to safe state in < 1ms:
//  1. Fault detected (1 cycle)
//  2. State transition to SAFE_STATE_ENTRY (1 cycle)
//  3. State transition to SAFE_STATE (1 cycle)
//  Total: 3 cycles = 7.5ns << 10ms ✓

// ============================================================================
// Formal Verification Properties
// ============================================================================

`ifdef FORMAL_VERIFICATION
    // Property 1: Power sequencing order
    // Must follow: OFF -> 1V -> 2V -> 3.3V sequence, no skipping
    property power_sequence_order;
        @ (posedge clk)
        ((current_state == STATE_STAGE1_SETTLE) |->
         (##1 current_state == STATE_STAGE2_RAMP));
    endproperty
    assert property (power_sequence_order);
    
    // Property 2: Safe state entry on fault
    // VDD fault must trigger safe state transition
    property safe_state_on_fault;
        @ (posedge clk)
        ((current_state == STATE_RUNNING && vdd_fault) |->
         ##[1:2] (current_state == STATE_SAFE_STATE_ENTRY ||
                  current_state == STATE_SAFE_STATE));
    endproperty
    assert property (safe_state_on_fault);
    
    // Property 3: Supply enable stability in RUNNING
    // Supply must remain enabled during normal operation
    property supply_enabled_running;
        @ (posedge clk)
        ((current_state == STATE_RUNNING) |->
         (supply_enable == 1'b1));
    endproperty
    assert property (supply_enabled_running);
`endif

// ============================================================================
// Safety Assertions
// ============================================================================

always @(posedge clk) begin
    // Verify FSM state validity
    assert (current_state inside {
        STATE_POWEROFF, STATE_STAGE1_RAMP, STATE_STAGE1_SETTLE,
        STATE_STAGE2_RAMP, STATE_STAGE2_SETTLE, STATE_STAGE3_RAMP,
        STATE_STAGE3_SETTLE, STATE_RUNNING, STATE_SAFE_STATE_ENTRY,
        STATE_SAFE_STATE, STATE_SHUTDOWN
    }) else $error("Invalid supply sequencer state");
    
    // Verify safe state entry completes within timing budget
    if (current_state == STATE_SAFE_STATE_ENTRY) begin
        assert (##1 (current_state == STATE_SAFE_STATE))
            else $error("Safe state entry not completed in time");
    end
end

endmodule
