; NOTE: Assertions have been autogenerated by utils/update_mir_test_checks.py
; RUN: llc -mtriple=amdgcn-mesa-mesa3d -global-isel -stop-after=irtranslator -o - %s | FileCheck %s

declare { float, i1 } @llvm.amdgcn.div.scale.f32(float, float, i1)

define amdgpu_ps void @test_div_scale(float %arg0, float %arg1) {
  ; CHECK-LABEL: name: test_div_scale
  ; CHECK: bb.1 (%ir-block.0):
  ; CHECK:   liveins: $vgpr0, $vgpr1
  ; CHECK:   [[COPY:%[0-9]+]]:_(s32) = COPY $vgpr0
  ; CHECK:   [[COPY1:%[0-9]+]]:_(s32) = COPY $vgpr1
  ; CHECK:   [[DEF:%[0-9]+]]:_(p1) = G_IMPLICIT_DEF
  ; CHECK:   [[DEF1:%[0-9]+]]:_(p1) = G_IMPLICIT_DEF
  ; CHECK:   [[INT:%[0-9]+]]:_(s32), [[INT1:%[0-9]+]]:_(s1) = G_INTRINSIC intrinsic(@llvm.amdgcn.div.scale), [[COPY]](s32), [[COPY1]](s32), -1
  ; CHECK:   [[SEXT:%[0-9]+]]:_(s32) = G_SEXT [[INT1]](s1)
  ; CHECK:   G_STORE [[INT]](s32), [[DEF]](p1) :: (store 4 into `float addrspace(1)* undef`, addrspace 1)
  ; CHECK:   G_STORE [[SEXT]](s32), [[DEF1]](p1) :: (store 4 into `i32 addrspace(1)* undef`, addrspace 1)
  ; CHECK:   S_ENDPGM 0
  %call = call { float, i1 } @llvm.amdgcn.div.scale.f32(float %arg0, float %arg1, i1 true)
  %extract0 = extractvalue { float, i1 } %call, 0
  %extract1 = extractvalue { float, i1 } %call, 1
  %ext = sext i1 %extract1 to i32
  store float %extract0, float addrspace(1)* undef
  store i32 %ext, i32 addrspace(1)* undef
  ret void
}
