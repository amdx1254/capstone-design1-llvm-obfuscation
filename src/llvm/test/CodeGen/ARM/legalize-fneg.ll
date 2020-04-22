; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc -mtriple=arm-eabi -float-abi=soft  -verify-machineinstrs < %s \
; RUN:   | FileCheck --check-prefixes=ARM %s
; RUN: llc -mtriple=arm-eabi -float-abi=soft  -verify-machineinstrs < %s \
; RUN:   | FileCheck --check-prefixes=NOLIB %s

; Check Y = FNEG(X) -> Y = X ^ sign mask and no lib call is generated.
define void @test1(float* %a, float* %b) {
; ARM-LABEL: test1:
; ARM:       @ %bb.0: @ %entry
; ARM-NEXT:    ldr r1, [r1]
; ARM-NEXT:    eor r1, r1, #-2147483648
; ARM-NEXT:    str r1, [r0]
; ARM-NEXT:    mov pc, lr
; NOLIB-LABEL:  test1:
; NOLIB:       eor
; NOLIB-NOT:   bl __aeabi_fsub
entry:
  %0 = load float, float* %b
  %neg = fneg float %0
  store float %neg, float* %a
  ret void
}

define void @test2(double* %a, double* %b) {
; ARM-LABEL: test2:
; ARM:       @ %bb.0: @ %entry
; ARM-NEXT:    ldr r2, [r1]
; ARM-NEXT:    ldr r1, [r1, #4]
; ARM-NEXT:    str r2, [r0]
; ARM-NEXT:    eor r1, r1, #-2147483648
; ARM-NEXT:    str r1, [r0, #4]
; ARM-NEXT:    mov pc, lr
; NOLIB-LABEL:  test2:
; NOLIB:       eor
; NOLIB-NOT:   bl __aeabi_dsub
entry:
  %0 = load double, double* %b
  %neg = fneg double %0
  store double %neg, double* %a
  ret void
}

define void @test3(fp128* %a, fp128* %b) {
; ARM-LABEL: test3:
; ARM:       @ %bb.0: @ %entry
; ARM-NEXT:    ldm r1, {r2, r3, r12}
; ARM-NEXT:    ldr r1, [r1, #12]
; ARM-NEXT:    stm r0, {r2, r3, r12}
; ARM-NEXT:    eor r1, r1, #-2147483648
; ARM-NEXT:    str r1, [r0, #12]
; ARM-NEXT:    mov pc, lr
; NOLIB-LABEL: test3:
; NOLIB:       eor
; NOLIB-NOT:   bl __subtf3
entry:
  %0 = load fp128, fp128* %b
  %neg = fneg fp128 %0
  store fp128 %neg, fp128* %a
  ret void
}
