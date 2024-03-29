; This test makes sure that div instructions are properly eliminated.
;

; RUN: llvm-as < %s | opt -instcombine | llvm-dis | not grep div

implementation

int %test1(int %A) {
	%B = div int %A, 1
	ret int %B
}

uint %test2(uint %A) {
	%B = div uint %A, 8   ; => Shift
	ret uint %B
}

int %test3(int %A) {
	%B = div int 0, %A    ; => 0, don't need to keep traps
	ret int %B
}

int %test4(int %A) {
	%B = div int %A, -1    ; 0-A
	ret int %B
}
