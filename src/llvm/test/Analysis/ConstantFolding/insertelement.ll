; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt < %s -constprop -S | FileCheck %s


define <4 x i32> @insertelement_fixedlength_constant() {
; CHECK-LABEL: @insertelement_fixedlength_constant(
; CHECK-NEXT:    ret <4 x i32> <i32 1, i32 undef, i32 undef, i32 undef>
;
  %i = insertelement <4 x i32> undef, i32 1, i32 0
  ret <4 x i32> %i
}

define <vscale x 4 x i32> @insertelement_scalable_constant() {
; CHECK-LABEL: @insertelement_scalable_constant(
; CHECK-NEXT:    ret <vscale x 4 x i32> insertelement (<vscale x 4 x i32> undef, i32 1, i32 0)
;
  %i = insertelement <vscale x 4 x i32> undef, i32 1, i32 0
  ret <vscale x 4 x i32> %i
}
