;ostanek
MOV A, 20 
MOV B, 7
MOV C, A
DIV  B
MUL B
SUB C, A

;-------------------
;zaporedna stevila
MOV A, 13

zanka:
PUSH A
INC A
CMP A, 43
JNC stop
JMP zanka

stop:
HLT

;-----------------------------------
;menjava vrednosti v pomnilniku
MOV [A], A ;premaknemo v pomnilnik
MOV [B], B

PUSH [A] ;izrpaznimo A
MOV A, [B] ;premaknemo vrednost shranjeno v B v A
POP B	;vzamemo vrednost iz sklada in jo damo v B

;---------------------------------------