module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res homOfLinear homOfLinear_app isoOfLinear toMod fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover germ_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply stalkLinear freeModule)

namespace GlobalTheory.VB

variable {X Y : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens} {r s : ℕ}

section Integral

variable [IsIntegral X]

theorem genericPoint_mem {x : X} (hx : x ∈ V) : genericPoint X ∈ V :=
  (genericPoint_specializes x).mem_open V.isOpen hx

variable (F) in
abbrev genStalk : Type := (F.presheaf.stalk (genericPoint X) :)

variable (F) in
def genRank : ℕ := Module.finrank X.functionField (genStalk F)

theorem IsVB.genRank_eq (h : IsVB F r) : genRank F = r := h.finrank_stalk _

theorem genRank_eq_zero_iff [IsFiniteQC F] : genRank F = 0 ↔ genericPoint X ∉ QCoh.support F :=
  (Module.finrank_zero_iff (R := X.functionField)).trans QCoh.notMem_support_iff.symm

theorem genRank_shortExact {S : ShortComplex X.Modules} (hS : S.ShortExact) [IsFiniteQC S.X₂] :
    genRank S.X₂ = genRank S.X₁ + genRank S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have e := (QCoh.exact_iff_stalkLinear S).1 hS.exact (genericPoint X)
  have h := LinearMap.finrank_range_add_finrank_ker (K := X.functionField)
    (stalkLinear S.g (genericPoint X))
  rw [LinearMap.range_eq_top.2 (QCoh.stalkLinear_surjective S.g _), finrank_top, e.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj (QCoh.stalkLinear_injective S.f _)] at h
  exact h.symm.trans (add_comm _ _)

theorem genRank_cokernel (i : G ⟶ F) [Mono i] [h : IsFiniteQC F] :
    genRank F = genRank G + genRank (cokernel i) :=
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  have := @genRank_shortExact _ _ _ hS h
  this

end Integral

section Curves

variable (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]

structure IsProperCurve : Prop where

  isIntegral : IsIntegral C

  dim_eq : topologicalKrullDim C = 1

  isProper : IsProper (strHom k (X := C))

structure IsProjCurve : Prop where

  isIntegral : IsIntegral C

  dim_eq : topologicalKrullDim C = 1

  isProjOver : IsProjOver (strHom k (X := C))

variable {k C}

omit [Field k] [Algebra k Γ(C, ⊤)] in
theorem suppDim_le_zero [IsIntegral C] (hd : topologicalKrullDim C = 1) {F : C.Modules} [IsFiniteQC F]
    (h : genRank F = 0) : QCoh.suppDim F ≤ 0 := by
  have := topologicalKrullDim_add_one_le (QCoh.isClosed_support F) isClosed_univ
    fun x _ => ⟨genericPoint C, trivial, genRank_eq_zero_iff.1 h, genericPoint_specializes x⟩
  have e : topologicalKrullDim (Set.univ : Set C) = 1 := by
    rw [← hd, ← QCoh.suppDim_structureModule, QCoh.suppDim, QCoh.support_structureModule]
  rw [e] at this
  exact ENat.WithBot.add_le_add_one_right_iff.1 (this.trans_eq (zero_add 1).symm)

end Curves

section Degree

variable (k : Type) [Field k] [Algebra k Γ(X, ⊤)]

def degOfRank (F : X.Modules) (r : ℕ) : ℤ := chi k F - r * chi k (structureModule X)

variable [IsIntegral X]

def deg (F : X.Modules) : ℤ := degOfRank k F (genRank F)

theorem deg_def : deg k F = chi k F - genRank F * chi k (structureModule X) := rfl

variable {k}

namespace IsProjCurve

variable (hC : IsProjCurve k X)
include hC

end IsProjCurve

variable (k) in
def degLB (L : LB X) : ℤ := deg k (toMod L)

variable {L M N : LB X}

theorem degLB_eq (hL : L.IsLB) : degLB k L = chi k (toMod L) - chi k (structureModule X) := by
  rw [degLB, deg_def, (isVB_toMod hL).genRank_eq]; simp

theorem IsProjCurve.degLB_eq_interNum (hC : IsProjCurve k X) (hL : L.IsLB) :
    degLB k L = interNum k (structureModule X) ![L] := by
  obtain ⟨_, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hC.isProjOver
  have hd := CechPic.isLB_dual hL
  have e₁ := interNum_one_of_cls_eq_add (k := k) hA hC.dim_eq (LB.isLB_triv X) hd hL
    (CechPic.cls_dual_add hL).symm
  have e₂ : interNum k (structureModule X) ![LB.triv X] = 0 :=
    interNum_eq_zero_of_cls_eq_zero k _ (isLB_vecOne (LB.isLB_triv X)) 0 rfl
  have e₃ : interNum k (structureModule X) ![CechPic.dual L] =
      chi k (structureModule X) - chi k (twist (structureModule X) L) :=
    (interNum_cons_of_cls_eq_neg k _ (P := ![]) hd isEmptyElim hL
      (by rw [CechPic.cls_dual hL, neg_neg])).trans
      (congrArg₂ (· - ·) (interNum_of_isEmpty k _ _) (interNum_of_isEmpty k _ _))
  rw [degLB_eq hL, ← chi_congr k (Twist.unitTwistIso L)]
  change chi k (twist (structureModule X) L) - _ = _
  omega

namespace IsMaxSubDeg

variable {P Q : ℤ}

end IsMaxSubDeg

end Degree

section Line

open ProjSpace ProjCoh

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type) [Field k]

end Line

section Prod

end Prod

end GlobalTheory.VB
