db 0

org $8000
.reset:

; write 10 down to 1 to $cafe
; tests branch offsets
ldx #$10
.loop:
stx $cafe
dex
bne .loop

.done:
  jmp .done


; no-op interrupt handlers
.irq:
 rti
.nmi:
 rti

; vectors
org $FFFA
dw .nmi
dw .reset
dw .irq
