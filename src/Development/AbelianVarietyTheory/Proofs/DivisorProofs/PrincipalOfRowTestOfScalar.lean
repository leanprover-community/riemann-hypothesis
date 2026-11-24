module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Module NumberField
open scoped InnerProductSpace Matrix
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.BasicNotions Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult

namespace GlobalTheory.OneFormTest

theorem model_of_pres {H Γ : Type} [Group H] [Group Γ] {ι : Γ →* H} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup H}
    {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (H → W))
    (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) (j : S.Forms →ₛₗ[σ] M.H) (hj : ∀ x, M.e (j x) = P.extL x) :
    (∀ x y, ⟪j x, j y⟫_ℂ = σ (S.csum x.1 y.1)) ∧ Function.Injective j ∧ Submodule.span ℂ (Set.range j) = ⊤ := by
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ P
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [hM.2.2, hj, hj]
    exact h3 x y
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h4 : P.extL x = 0 := by rw [← hj, hx, map_zero]

    rw [← S.basis.sum_repr x, map_sum] at h4
    simp only [map_smulₛₗ] at h4
    have h5 := Fintype.linearIndependent_iff.1 h1 _ h4
    refine S.basis.repr.injective (Finsupp.ext fun i => ?_)
    rw [(map_eq_zero _).1 (h5 i), map_zero, Finsupp.zero_apply]
  · apply Submodule.map_injective_of_injective hM.1
    rw [Submodule.map_top, hM.2.1, Submodule.map_span, ← Set.range_comp, show M.e ∘ j = P.extL from funext hj, h2]

section Concrete

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem model_jX (hH : R.models_HX) (hj : R.models_jX) (t : T) :
    (∀ x y : (A.MtildeCSD t).Forms, ⟪R.jX t x, R.jX t y⟫_ℂ = D.what₂.embLL ((A.MtildeCSD t).csum x.1 y.1)) ∧
      Function.Injective (R.jX t) ∧ Submodule.span ℂ (Set.range (R.jX t)) = ⊤ :=
  model_of_pres (S := A.MtildeCSD t) (R.B.R t).pres (R.HX t) (hH t) (R.jX t) (hj t)

end Concrete

end GlobalTheory.OneFormTest
