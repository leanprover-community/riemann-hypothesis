module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOverStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

def constHom {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) : Ω →+* ring ε.range where
  toFun c := ⟨fun _ => ε c, mem_ring_of_inR ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).2 _ ⟨c, rfl⟩)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def evAt (E : Subring ℂ) (τ : ℍ) : ring E →+* ℂ := (Pi.evalRingHom (fun _ : ℍ => ℂ) τ).comp (ring E).subtype

theorem evAt_apply (E : Subring ℂ) (τ : ℍ) (x : ring E) : evAt E τ x = (x : ℍ → ℂ) τ := rfl

theorem evAt_comp_constHom {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (τ : ℍ) :
    (evAt ε.range τ).comp (constHom ε) = ε := by
  ext c; rfl

theorem io_comp_constHom {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Frac Ω ε) :
    T.io.comp (constHom ε) = algebraMap Ω T.K := by
  ext c; exact T.io_c c _ rfl

theorem isIntegral_io_adjoin_j (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (a : ring ε.range) (ha : (a : ℍ → ℂ) = jT) (b : ring ε.range) :
    IsIntegral (IntermediateField.adjoin Ω {T.io a}) (T.io b) := by
  set L := IntermediateField.adjoin Ω {T.io a}
  obtain ⟨n, c, hc, hrel⟩ := GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver ε.range b (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2)
  have hl : ∀ i, c i ∈ Polynomial.lifts ε := fun i =>
    (Polynomial.lifts_iff_coeff_lifts _).2 fun k => RingHom.mem_range.1 (hc i k)
  choose d hd using fun i => (Polynomial.mem_lifts (c i)).1 (hl i)
  let xa : L := ⟨T.io a, IntermediateField.mem_adjoin_simple_self Ω _⟩
  let φ : Polynomial Ω →ₐ[Ω] L := Polynomial.aeval xa

  have hr : b ^ n + ∑ i, (d i).eval₂ (constHom ε) a * b ^ (i : ℕ) = 0 := by
    apply Subtype.ext; funext τ
    have h := hrel τ
    have key : evAt ε.range τ (b ^ n + ∑ i, (d i).eval₂ (constHom ε) a * b ^ (i : ℕ)) = 0 := by

      simp only [map_add (f := _), map_sum, map_mul, map_pow, Polynomial.hom_eval₂, evAt_comp_constHom,
      evAt_apply, ha]
      simpa [← Polynomial.eval_map, hd] using h
    simpa [evAt_apply] using key
  have hK : T.io b ^ n + ∑ i, Polynomial.aeval (T.io a) (d i) * T.io b ^ (i : ℕ) = 0 := by
    have := congrArg T.io hr

    simp only [map_add (f := _), map_sum, map_mul, map_pow, Polynomial.hom_eval₂, io_comp_constHom, map_zero] at this
    simpa [Polynomial.aeval_def] using this
  refine ⟨Polynomial.X ^ n + ∑ i, Polynomial.C (φ (d i)) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  have hφ : ∀ i, algebraMap L T.K (φ (d i)) = Polynomial.aeval (T.io a) (d i) := fun i => by
    show L.val (φ (d i)) = _
    rw [← Polynomial.aeval_algHom_apply L.val xa (d i)]
    rfl
  have hsum := map_sum (Polynomial.eval₂AddMonoidHom (algebraMap L T.K) (T.io b))
    (fun i => Polynomial.C (φ (d i)) * Polynomial.X ^ (i : ℕ)) Finset.univ
  change Polynomial.eval₂ (algebraMap L T.K) (T.io b) (∑ i, Polynomial.C (φ (d i)) * Polynomial.X ^ (i : ℕ)) = _ at hsum
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, hsum, Polynomial.eval₂AddMonoidHom_apply,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, hφ]
  exact hK

theorem frac_isAlgebraic_adjoin_j : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (a : GlobalTheory.FN.ring ε.range), (a : ℍ → ℂ) = jT → ∀ f : T.K, IsAlgebraic (IntermediateField.adjoin Ω {T.io a}) f := by
  intro Ω _ _ _ ε T a ha f
  obtain ⟨x, y, hy, hxy⟩ := T.io_surj f
  have hy' : T.io y ≠ 0 := fun h => hy (T.io_inj (h.trans (map_zero T.io).symm))
  have hf : f = T.io x * (T.io y)⁻¹ := by rw [← hxy, mul_inv_cancel_right₀ hy']
  rw [hf]
  exact (isIntegral_io_adjoin_j Ω ε T a ha x).isAlgebraic.mul (isIntegral_io_adjoin_j Ω ε T a ha y).isAlgebraic.inv

end GlobalTheory.FN
