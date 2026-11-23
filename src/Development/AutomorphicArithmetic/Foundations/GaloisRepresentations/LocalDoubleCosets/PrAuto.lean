module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.prAuto :
    PrAuto := by
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ s p hp hs hper hsB hχ
  have hit : ∀ n (b : G), b ∈ B → s^[n] b ∈ B := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      rw [Function.iterate_succ_apply']
      exact hsB _ (ih b hb)
  have hleft : ∀ g, s^[p - 1] (s g) = g := by
    intro g
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact hper g
  have hright : ∀ g, s (s^[p - 1] g) = g := by
    intro g
    rw [← Function.iterate_succ_apply' s, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact hper g
  let σ : B ≃ₜ* B :=
    { toFun := fun b => ⟨s b, hsB _ b.2⟩
      invFun := fun b => ⟨s^[p - 1] b, hit _ _ b.2⟩
      left_inv := fun b => Subtype.ext (hleft b)
      right_inv := fun b => Subtype.ext (hright b)
      map_mul' := fun a b => Subtype.ext (map_mul s (a : G) (b : G))
      continuous_toFun := (hs.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((hs.iterate _).comp continuous_subtype_val).subtype_mk _ }
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B :=
    inferInstanceAs (SecondCountableTopology {x // x ∈ (B : Set G)})
  haveI hν : (Measure.map σ μ).IsHaarMeasure := σ.isHaarMeasure_map μ
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map σ μ) μ
  refine ⟨Measure.haarScalarFactor (Measure.map σ μ) μ,
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, fun f g => ?_⟩
  have hint : ∀ b : B, (χ b : ℂ) * (f ∘ s) ((b : G)⁻¹ * g) =
      (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) := by
    intro b
    rw [hχ b (σ b) rfl]
    simp [σ, map_mul, map_inv]
  have hm : ∫ c, (χ c : ℂ) * f ((c : G)⁻¹ * s g) ∂(Measure.map σ μ) =
      ∫ b, (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) ∂μ :=
    integral_map_equiv σ.toHomeomorph.toMeasurableEquiv (fun c : B => (χ c : ℂ) * f ((c : G)⁻¹ * s g))
  unfold pr
  simp_rw [hint]
  rw [← hm]
  conv_lhs => rw [heq]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
