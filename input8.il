function $test() {
@start
   %e.5 =l alloc8 8
   %ie.6 =l alloc8 8
@l10
   jnz 1, @l11, @l12
@l11
   %t77 =l load %e.5
   %t76 =w call $SDL_PollEvent(l %t77, ...)
   jnz %t76, @l13, @l14
@l13
   %t81 =l load %ie.6
   %t80 =l add %t81, 0
   %t79 =w load %t80
   %t78 =w ceqw %t79, 769
   jnz %t78, @l16, @l17
@l16
   jmp @l12
@l17
@l14
   jmp @l10
@l12
    ret
}
