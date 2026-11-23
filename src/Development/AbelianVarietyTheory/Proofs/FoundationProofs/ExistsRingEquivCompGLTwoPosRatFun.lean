module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverCompGLTwoPosRatStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_mem_ring (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) {f : ℍ → ℂ} (hf : f ∈ ring E) :
    cmp g f ∈ ring E :=
  ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1 _).2 (GlobalTheory.T.hasSomeLevelOver_compGLTwoPosRat E g f hE (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver E).1 f).1 hf))

noncomputable def cmpHom (E : Subring ℂ) (g : GQ)
    (hE : ∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) : ring E →+* ring E where
  toFun a := ⟨cmp g a, cmp_mem_ring E g hE a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cmp_cmp_inv (g : GQ) (f : ℍ → ℂ) : cmp g (cmp g⁻¹ f) = f := by
  rw [← GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.1, inv_mul_cancel, GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.1]

theorem cmp_inv_cmp (g : GQ) (f : ℍ → ℂ) : cmp g⁻¹ (cmp g f) = f := by
  rw [← GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.1, mul_inv_cancel, GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.1]

theorem cmp_ringEquiv : ∀ (E : Subring ℂ) (g : GQ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    ∃ σ : GlobalTheory.FN.ring E ≃+* GlobalTheory.FN.ring E, ∀ a, ((σ a : GlobalTheory.FN.ring E) : ℍ → ℂ) = GlobalTheory.FN.cmp g a := by
  intro E g hE
  refine ⟨{ cmpHom E g hE with
    invFun := cmpHom E g⁻¹ hE
    left_inv := fun a => Subtype.ext (cmp_inv_cmp g a)
    right_inv := fun a => Subtype.ext (cmp_cmp_inv g a) }, fun a => rfl⟩

end GlobalTheory.FN
