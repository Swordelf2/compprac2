export function w $bar() {
@start
    %x =w copy 1
    jnz %x, @d1, @dn
@d1
    %x =w copy 2
    jmp @end
@dn
    jnz %x, @d2, @d3
@d2
    %x =w copy 3
    jmp @end
@d3
    %x =w copy 4
    jmp @end
@end
    ret %x
}
