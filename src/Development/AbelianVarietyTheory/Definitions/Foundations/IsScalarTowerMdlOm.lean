module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
public import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
public import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
public import ReciprocityTheory.GaloisValuations.Global

@[expose] public section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.ZetaB

open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.NeedB GlobalTheory.KEdge

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

attribute [local instance] algMdl

attribute [local instance] isScalarTower_mdl_om

open Classical in
def unitOf (X : Tower Ω ε) (a : X.K) : X.Kˣ :=
  letI := Classical.propDecidable (a = 0)
  if h : a = 0 then 1 else Units.mk0 a h

def clsHat (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.K) : X.Khat l :=
  AdicCompletion.of (idl l) (X.Kl l) ((1 : ℤ_[l]) ⊗ₜ Additive.ofMul (unitOf X a))

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.eval_clsHat (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ)
    [Fact l.Prime] (n : ℕ) (a : X.K) :
    AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n
        (_root_.GlobalTheory.ZetaB.clsHat X l a) =
      X.cls l n (_root_.GlobalTheory.ZetaB.unitOf X a) := by
  unfold _root_.GlobalTheory.ZetaB.clsHat
  rw [AdicCompletion.eval_of]
  rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.unitOf_val (X : _root_.GlobalTheory.KZ.Tower Ω ε) {a : X.K}
    (ha : a ≠ 0) : ((_root_.GlobalTheory.ZetaB.unitOf X a : (X.K)ˣ) : X.K) = a := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dite_eq_right ha]
  rfl

open scoped MatrixGroups TensorProduct in
open Matrix in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
attribute [local instance] _root_.GlobalTheory.K4.algMdl in
theorem _root_.GlobalTheory.ZetaB.unitOf_zero (X : _root_.GlobalTheory.KZ.Tower Ω ε) :
    _root_.GlobalTheory.ZetaB.unitOf X 0 = 1 := by
  unfold _root_.GlobalTheory.ZetaB.unitOf
  rw [dite_eq_left rfl]

end GlobalTheory.ZetaB
