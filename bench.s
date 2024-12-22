.text
.balign 4
.globl _v_F5_c_nothing
_v_F5_c_nothing:
	stp	x29, x30, [sp, -16]!
	mov	x29, sp
	mov	w0, #0
	ldp	x29, x30, [sp], 16
	ret
/* end function v_F5_c_nothing */

.text
.balign 4
.globl _v_F6_c_nothing
_v_F6_c_nothing:
	stp	x29, x30, [sp, -16]!
	mov	x29, sp
	mov	w0, #0
	ldp	x29, x30, [sp], 16
	ret
/* end function v_F6_c_nothing */

.text
.balign 4
.globl _main
_main:
	stp	x29, x30, [sp, -16]!
	mov	x29, sp
	adrp	x0, _string.5@page
	add	x0, x0, _string.5@pageoff
	bl	_v_F5_c_nothing
	adrp	x0, _string.7@page
	add	x0, x0, _string.7@pageoff
	bl	_v_F6_c_nothing
	mov	w0, #0
	ldp	x29, x30, [sp], 16
	ret
/* end function main */

.data
.balign 8
_string.1:
	.ascii "hello"
/* end data */

.data
.balign 8
_string.2:
	.ascii "world!"
/* end data */

.data
.balign 8
_string.5:
	.ascii "hello"
/* end data */

.data
.balign 8
_string.7:
	.ascii "world!"
/* end data */

