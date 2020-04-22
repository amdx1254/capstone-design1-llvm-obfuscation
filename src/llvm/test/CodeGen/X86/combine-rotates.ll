; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+sse2 | FileCheck %s --check-prefixes=CHECK,SSE2
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx,+xop | FileCheck %s --check-prefixes=CHECK,XOP
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx2 | FileCheck %s --check-prefixes=CHECK,AVX2
; RUN: llc < %s -mtriple=x86_64-unknown-unknown -mattr=+avx512f,+avx512vl | FileCheck %s --check-prefixes=CHECK,AVX512

; fold (rot (rot x, c1), c2) -> rot x, c1+c2
define <4 x i32> @combine_vec_rot_rot(<4 x i32> %x) {
; SSE2-LABEL: combine_vec_rot_rot:
; SSE2:       # %bb.0:
; SSE2-NEXT:    movdqa {{.*#+}} xmm1 = [524288,131072,32768,8192]
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm0[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm1, %xmm0
; SSE2-NEXT:    pshufd {{.*#+}} xmm3 = xmm0[1,3,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm1 = xmm1[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm2, %xmm1
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm1[1,3,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm3 = xmm3[0],xmm2[0],xmm3[1],xmm2[1]
; SSE2-NEXT:    pshufd {{.*#+}} xmm0 = xmm0[0,2,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm1 = xmm1[0,2,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm0 = xmm0[0],xmm1[0],xmm0[1],xmm1[1]
; SSE2-NEXT:    por %xmm3, %xmm0
; SSE2-NEXT:    retq
;
; XOP-LABEL: combine_vec_rot_rot:
; XOP:       # %bb.0:
; XOP-NEXT:    vprotd {{.*}}(%rip), %xmm0, %xmm0
; XOP-NEXT:    retq
;
; AVX2-LABEL: combine_vec_rot_rot:
; AVX2:       # %bb.0:
; AVX2-NEXT:    vpsrlvd {{.*}}(%rip), %xmm0, %xmm1
; AVX2-NEXT:    vpsllvd {{.*}}(%rip), %xmm0, %xmm0
; AVX2-NEXT:    vpor %xmm1, %xmm0, %xmm0
; AVX2-NEXT:    retq
;
; AVX512-LABEL: combine_vec_rot_rot:
; AVX512:       # %bb.0:
; AVX512-NEXT:    vprolvd {{.*}}(%rip), %xmm0, %xmm0
; AVX512-NEXT:    retq
  %1 = lshr <4 x i32> %x, <i32 1, i32 2, i32 3, i32 4>
  %2 = shl <4 x i32> %x, <i32 31, i32 30, i32 29, i32 28>
  %3 = or <4 x i32> %1, %2
  %4 = lshr <4 x i32> %3, <i32 12, i32 13, i32 14, i32 15>
  %5 = shl <4 x i32> %3, <i32 20, i32 19, i32 18, i32 17>
  %6 = or <4 x i32> %4, %5
  ret <4 x i32> %6
}

define <4 x i32> @combine_vec_rot_rot_splat(<4 x i32> %x) {
; SSE2-LABEL: combine_vec_rot_rot_splat:
; SSE2:       # %bb.0:
; SSE2-NEXT:    movdqa %xmm0, %xmm1
; SSE2-NEXT:    psrld $25, %xmm1
; SSE2-NEXT:    pslld $7, %xmm0
; SSE2-NEXT:    por %xmm1, %xmm0
; SSE2-NEXT:    retq
;
; XOP-LABEL: combine_vec_rot_rot_splat:
; XOP:       # %bb.0:
; XOP-NEXT:    vprotd $7, %xmm0, %xmm0
; XOP-NEXT:    retq
;
; AVX2-LABEL: combine_vec_rot_rot_splat:
; AVX2:       # %bb.0:
; AVX2-NEXT:    vpsrld $25, %xmm0, %xmm1
; AVX2-NEXT:    vpslld $7, %xmm0, %xmm0
; AVX2-NEXT:    vpor %xmm1, %xmm0, %xmm0
; AVX2-NEXT:    retq
;
; AVX512-LABEL: combine_vec_rot_rot_splat:
; AVX512:       # %bb.0:
; AVX512-NEXT:    vprold $7, %xmm0, %xmm0
; AVX512-NEXT:    retq
  %1 = lshr <4 x i32> %x, <i32 3, i32 3, i32 3, i32 3>
  %2 = shl <4 x i32> %x, <i32 29, i32 29, i32 29, i32 29>
  %3 = or <4 x i32> %1, %2
  %4 = lshr <4 x i32> %3, <i32 22, i32 22, i32 22, i32 22>
  %5 = shl <4 x i32> %3, <i32 10, i32 10, i32 10, i32 10>
  %6 = or <4 x i32> %4, %5
  ret <4 x i32> %6
}

define <4 x i32> @combine_vec_rot_rot_splat_zero(<4 x i32> %x) {
; CHECK-LABEL: combine_vec_rot_rot_splat_zero:
; CHECK:       # %bb.0:
; CHECK-NEXT:    retq
  %1 = lshr <4 x i32> %x, <i32 1, i32 1, i32 1, i32 1>
  %2 = shl <4 x i32> %x, <i32 31, i32 31, i32 31, i32 31>
  %3 = or <4 x i32> %1, %2
  %4 = lshr <4 x i32> %3, <i32 31, i32 31, i32 31, i32 31>
  %5 = shl <4 x i32> %3, <i32 1, i32 1, i32 1, i32 1>
  %6 = or <4 x i32> %4, %5
  ret <4 x i32> %6
}

; TODO - fold (select (icmp eq c, 0), x, (rot x, c)) -> rot x, c
define i32 @combine_rot_select_zero(i32, i32) {
; CHECK-LABEL: combine_rot_select_zero:
; CHECK:       # %bb.0:
; CHECK-NEXT:    movl %esi, %ecx
; CHECK-NEXT:    movl %edi, %eax
; CHECK-NEXT:    roll %cl, %eax
; CHECK-NEXT:    testl %esi, %esi
; CHECK-NEXT:    cmovel %edi, %eax
; CHECK-NEXT:    retq
  %3 = and i32 %1, 31
  %4 = shl i32 %0, %3
  %5 = sub i32 0, %1
  %6 = and i32 %5, 31
  %7 = lshr i32 %0, %6
  %8 = or i32 %4, %7
  %9 = icmp eq i32 %1, 0
  %10 = select i1 %9, i32 %0, i32 %8
  ret i32 %10
}

define <4 x i32> @combine_vec_rot_select_zero(<4 x i32>, <4 x i32>) {
; SSE2-LABEL: combine_vec_rot_select_zero:
; SSE2:       # %bb.0:
; SSE2-NEXT:    movdqa {{.*#+}} xmm2 = [31,31,31,31]
; SSE2-NEXT:    pand %xmm1, %xmm2
; SSE2-NEXT:    pxor %xmm3, %xmm3
; SSE2-NEXT:    pslld $23, %xmm2
; SSE2-NEXT:    paddd {{.*}}(%rip), %xmm2
; SSE2-NEXT:    cvttps2dq %xmm2, %xmm2
; SSE2-NEXT:    movdqa %xmm0, %xmm4
; SSE2-NEXT:    pmuludq %xmm2, %xmm4
; SSE2-NEXT:    pshufd {{.*#+}} xmm5 = xmm4[1,3,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm6 = xmm0[1,1,3,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm2[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm6, %xmm2
; SSE2-NEXT:    pshufd {{.*#+}} xmm6 = xmm2[1,3,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm5 = xmm5[0],xmm6[0],xmm5[1],xmm6[1]
; SSE2-NEXT:    pshufd {{.*#+}} xmm4 = xmm4[0,2,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm2[0,2,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm4 = xmm4[0],xmm2[0],xmm4[1],xmm2[1]
; SSE2-NEXT:    por %xmm5, %xmm4
; SSE2-NEXT:    pcmpeqd %xmm1, %xmm3
; SSE2-NEXT:    pand %xmm3, %xmm0
; SSE2-NEXT:    pandn %xmm4, %xmm3
; SSE2-NEXT:    por %xmm3, %xmm0
; SSE2-NEXT:    retq
;
; XOP-LABEL: combine_vec_rot_select_zero:
; XOP:       # %bb.0:
; XOP-NEXT:    vpand {{.*}}(%rip), %xmm1, %xmm2
; XOP-NEXT:    vpxor %xmm3, %xmm3, %xmm3
; XOP-NEXT:    vprotd %xmm2, %xmm0, %xmm2
; XOP-NEXT:    vpcomeqd %xmm3, %xmm1, %xmm1
; XOP-NEXT:    vblendvps %xmm1, %xmm0, %xmm2, %xmm0
; XOP-NEXT:    retq
;
; AVX2-LABEL: combine_vec_rot_select_zero:
; AVX2:       # %bb.0:
; AVX2-NEXT:    vpbroadcastd {{.*#+}} xmm2 = [31,31,31,31]
; AVX2-NEXT:    vpand %xmm2, %xmm1, %xmm2
; AVX2-NEXT:    vpxor %xmm3, %xmm3, %xmm3
; AVX2-NEXT:    vpsllvd %xmm2, %xmm0, %xmm4
; AVX2-NEXT:    vpbroadcastd {{.*#+}} xmm5 = [32,32,32,32]
; AVX2-NEXT:    vpsubd %xmm2, %xmm5, %xmm2
; AVX2-NEXT:    vpsrlvd %xmm2, %xmm0, %xmm2
; AVX2-NEXT:    vpor %xmm2, %xmm4, %xmm2
; AVX2-NEXT:    vpcmpeqd %xmm3, %xmm1, %xmm1
; AVX2-NEXT:    vblendvps %xmm1, %xmm0, %xmm2, %xmm0
; AVX2-NEXT:    retq
;
; AVX512-LABEL: combine_vec_rot_select_zero:
; AVX512:       # %bb.0:
; AVX512-NEXT:    vpandd {{.*}}(%rip){1to4}, %xmm1, %xmm2
; AVX512-NEXT:    vprolvd %xmm2, %xmm0, %xmm2
; AVX512-NEXT:    vptestnmd %xmm1, %xmm1, %k1
; AVX512-NEXT:    vmovdqa32 %xmm0, %xmm2 {%k1}
; AVX512-NEXT:    vmovdqa %xmm2, %xmm0
; AVX512-NEXT:    retq
  %3 = and <4 x i32> %1, <i32 31, i32 31, i32 31, i32 31>
  %4 = shl <4 x i32> %0, %3
  %5 = sub <4 x i32> zeroinitializer, %1
  %6 = and <4 x i32> %5, <i32 31, i32 31, i32 31, i32 31>
  %7 = lshr <4 x i32> %0, %6
  %8 = or <4 x i32> %4, %7
  %9 = icmp eq <4 x i32> %1, zeroinitializer
  %10 = select <4 x i1> %9, <4 x i32> %0, <4 x i32> %8
  ret <4 x i32> %10
}

define <4 x i32> @rotate_demanded_bits(<4 x i32>, <4 x i32>) {
; SSE2-LABEL: rotate_demanded_bits:
; SSE2:       # %bb.0:
; SSE2-NEXT:    pand {{.*}}(%rip), %xmm1
; SSE2-NEXT:    pslld $23, %xmm1
; SSE2-NEXT:    paddd {{.*}}(%rip), %xmm1
; SSE2-NEXT:    cvttps2dq %xmm1, %xmm1
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm0[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm1, %xmm0
; SSE2-NEXT:    pshufd {{.*#+}} xmm3 = xmm0[1,3,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm1 = xmm1[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm2, %xmm1
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm1[1,3,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm3 = xmm3[0],xmm2[0],xmm3[1],xmm2[1]
; SSE2-NEXT:    pshufd {{.*#+}} xmm0 = xmm0[0,2,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm1 = xmm1[0,2,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm0 = xmm0[0],xmm1[0],xmm0[1],xmm1[1]
; SSE2-NEXT:    por %xmm3, %xmm0
; SSE2-NEXT:    retq
;
; XOP-LABEL: rotate_demanded_bits:
; XOP:       # %bb.0:
; XOP-NEXT:    vpand {{.*}}(%rip), %xmm1, %xmm1
; XOP-NEXT:    vprotd %xmm1, %xmm0, %xmm0
; XOP-NEXT:    retq
;
; AVX2-LABEL: rotate_demanded_bits:
; AVX2:       # %bb.0:
; AVX2-NEXT:    vpbroadcastd {{.*#+}} xmm2 = [30,30,30,30]
; AVX2-NEXT:    vpand %xmm2, %xmm1, %xmm1
; AVX2-NEXT:    vpsllvd %xmm1, %xmm0, %xmm2
; AVX2-NEXT:    vpbroadcastd {{.*#+}} xmm3 = [32,32,32,32]
; AVX2-NEXT:    vpsubd %xmm1, %xmm3, %xmm1
; AVX2-NEXT:    vpsrlvd %xmm1, %xmm0, %xmm0
; AVX2-NEXT:    vpor %xmm0, %xmm2, %xmm0
; AVX2-NEXT:    retq
;
; AVX512-LABEL: rotate_demanded_bits:
; AVX512:       # %bb.0:
; AVX512-NEXT:    vpandd {{.*}}(%rip){1to4}, %xmm1, %xmm1
; AVX512-NEXT:    vprolvd %xmm1, %xmm0, %xmm0
; AVX512-NEXT:    retq
  %3 = and <4 x i32> %1, <i32 30, i32 30, i32 30, i32 30>
  %4 = shl <4 x i32> %0, %3
  %5 = sub nsw <4 x i32> zeroinitializer, %3
  %6 = and <4 x i32> %5, <i32 30, i32 30, i32 30, i32 30>
  %7 = lshr <4 x i32> %0, %6
  %8 = or <4 x i32> %7, %4
  ret <4 x i32> %8
}

define <4 x i32> @rotate_demanded_bits_2(<4 x i32>, <4 x i32>) {
; SSE2-LABEL: rotate_demanded_bits_2:
; SSE2:       # %bb.0:
; SSE2-NEXT:    pand {{.*}}(%rip), %xmm1
; SSE2-NEXT:    pslld $23, %xmm1
; SSE2-NEXT:    paddd {{.*}}(%rip), %xmm1
; SSE2-NEXT:    cvttps2dq %xmm1, %xmm1
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm0[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm1, %xmm0
; SSE2-NEXT:    pshufd {{.*#+}} xmm3 = xmm0[1,3,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm1 = xmm1[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm2, %xmm1
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm1[1,3,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm3 = xmm3[0],xmm2[0],xmm3[1],xmm2[1]
; SSE2-NEXT:    pshufd {{.*#+}} xmm0 = xmm0[0,2,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm1 = xmm1[0,2,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm0 = xmm0[0],xmm1[0],xmm0[1],xmm1[1]
; SSE2-NEXT:    por %xmm3, %xmm0
; SSE2-NEXT:    retq
;
; XOP-LABEL: rotate_demanded_bits_2:
; XOP:       # %bb.0:
; XOP-NEXT:    vpand {{.*}}(%rip), %xmm1, %xmm1
; XOP-NEXT:    vprotd %xmm1, %xmm0, %xmm0
; XOP-NEXT:    retq
;
; AVX2-LABEL: rotate_demanded_bits_2:
; AVX2:       # %bb.0:
; AVX2-NEXT:    vpbroadcastd {{.*#+}} xmm2 = [23,23,23,23]
; AVX2-NEXT:    vpand %xmm2, %xmm1, %xmm1
; AVX2-NEXT:    vpsllvd %xmm1, %xmm0, %xmm2
; AVX2-NEXT:    vpbroadcastd {{.*#+}} xmm3 = [32,32,32,32]
; AVX2-NEXT:    vpsubd %xmm1, %xmm3, %xmm1
; AVX2-NEXT:    vpsrlvd %xmm1, %xmm0, %xmm0
; AVX2-NEXT:    vpor %xmm0, %xmm2, %xmm0
; AVX2-NEXT:    retq
;
; AVX512-LABEL: rotate_demanded_bits_2:
; AVX512:       # %bb.0:
; AVX512-NEXT:    vpandd {{.*}}(%rip){1to4}, %xmm1, %xmm1
; AVX512-NEXT:    vprolvd %xmm1, %xmm0, %xmm0
; AVX512-NEXT:    retq
  %3 = and <4 x i32> %1, <i32 23, i32 23, i32 23, i32 23>
  %4 = shl <4 x i32> %0, %3
  %5 = sub nsw <4 x i32> zeroinitializer, %3
  %6 = and <4 x i32> %5, <i32 31, i32 31, i32 31, i32 31>
  %7 = lshr <4 x i32> %0, %6
  %8 = or <4 x i32> %7, %4
  ret <4 x i32> %8
}

define <4 x i32> @rotate_demanded_bits_3(<4 x i32>, <4 x i32>) {
; SSE2-LABEL: rotate_demanded_bits_3:
; SSE2:       # %bb.0:
; SSE2-NEXT:    paddd %xmm1, %xmm1
; SSE2-NEXT:    pand {{.*}}(%rip), %xmm1
; SSE2-NEXT:    pslld $23, %xmm1
; SSE2-NEXT:    paddd {{.*}}(%rip), %xmm1
; SSE2-NEXT:    cvttps2dq %xmm1, %xmm1
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm0[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm1, %xmm0
; SSE2-NEXT:    pshufd {{.*#+}} xmm3 = xmm0[1,3,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm1 = xmm1[1,1,3,3]
; SSE2-NEXT:    pmuludq %xmm2, %xmm1
; SSE2-NEXT:    pshufd {{.*#+}} xmm2 = xmm1[1,3,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm3 = xmm3[0],xmm2[0],xmm3[1],xmm2[1]
; SSE2-NEXT:    pshufd {{.*#+}} xmm0 = xmm0[0,2,2,3]
; SSE2-NEXT:    pshufd {{.*#+}} xmm1 = xmm1[0,2,2,3]
; SSE2-NEXT:    punpckldq {{.*#+}} xmm0 = xmm0[0],xmm1[0],xmm0[1],xmm1[1]
; SSE2-NEXT:    por %xmm3, %xmm0
; SSE2-NEXT:    retq
;
; XOP-LABEL: rotate_demanded_bits_3:
; XOP:       # %bb.0:
; XOP-NEXT:    vpaddd %xmm1, %xmm1, %xmm1
; XOP-NEXT:    vpand {{.*}}(%rip), %xmm1, %xmm1
; XOP-NEXT:    vprotd %xmm1, %xmm0, %xmm0
; XOP-NEXT:    retq
;
; AVX2-LABEL: rotate_demanded_bits_3:
; AVX2:       # %bb.0:
; AVX2-NEXT:    vpaddd %xmm1, %xmm1, %xmm1
; AVX2-NEXT:    vpbroadcastd {{.*#+}} xmm2 = [30,30,30,30]
; AVX2-NEXT:    vpand %xmm2, %xmm1, %xmm1
; AVX2-NEXT:    vpsllvd %xmm1, %xmm0, %xmm2
; AVX2-NEXT:    vpbroadcastd {{.*#+}} xmm3 = [32,32,32,32]
; AVX2-NEXT:    vpsubd %xmm1, %xmm3, %xmm1
; AVX2-NEXT:    vpsrlvd %xmm1, %xmm0, %xmm0
; AVX2-NEXT:    vpor %xmm0, %xmm2, %xmm0
; AVX2-NEXT:    retq
;
; AVX512-LABEL: rotate_demanded_bits_3:
; AVX512:       # %bb.0:
; AVX512-NEXT:    vpaddd %xmm1, %xmm1, %xmm1
; AVX512-NEXT:    vpandd {{.*}}(%rip){1to4}, %xmm1, %xmm1
; AVX512-NEXT:    vprolvd %xmm1, %xmm0, %xmm0
; AVX512-NEXT:    retq
  %3 = shl <4 x i32> %1, <i32 1, i32 1, i32 1, i32 1>
  %4 = and <4 x i32> %3, <i32 30, i32 30, i32 30, i32 30>
  %5 = shl <4 x i32> %0, %4
  %6 = sub <4 x i32> zeroinitializer, %3
  %7 = and <4 x i32> %6, <i32 30, i32 30, i32 30, i32 30>
  %8 = lshr <4 x i32> %0, %7
  %9 = or <4 x i32> %5, %8
  ret <4 x i32> %9
}

; OSS Fuzz: https://bugs.chromium.org/p/oss-fuzz/issues/detail?id=9935
define i32 @fuzz9935() {
; CHECK-LABEL: fuzz9935:
; CHECK:       # %bb.0:
; CHECK-NEXT:    movl $-1, %eax
; CHECK-NEXT:    retq
  %1 = trunc i40 549755813887 to i32
  %2 = mul i32 %1, %1
  %3 = lshr i32 %2, %1
  %4 = or i32 %3, %2
  ret i32 %4
}
