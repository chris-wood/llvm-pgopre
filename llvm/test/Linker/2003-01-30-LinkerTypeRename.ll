; This fails because the linker renames the non-opaque type not the opaque 
; one...

; RUN: echo "%Ty = type opaque %GV = external global %Ty*" | llvm-as > %t.1.bc
; RUN: llvm-as < %s > %t.2.bc
; RUN: llvm-link %t.[12].bc | llvm-dis | grep '%Ty ' | not grep opaque

%Ty = type int

