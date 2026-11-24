module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

private lemma UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg {R K ι : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Finite ι] (L : Submodule R (ι → K)) (hL : L.FG) :
    ∃ b : R, b ≠ 0 ∧ ∀ y ∈ L, ∀ i : ι, ∃ c : R, algebraMap R K c = algebraMap R K b * y i := by
  obtain ⟨S, rfl⟩ := hL
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : S × ι => (p.1 : ι → K) p.2)
  refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
  intro y hy i
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ := hb (⟨x, hx⟩, i)
    exact ⟨c, by rw [hc, Algebra.smul_def]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [map_add (f := _), hc, hd, Pi.add_apply, mul_add]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    exact ⟨a * c, by rw [map_mul, hc, Pi.smul_apply, Algebra.smul_def]; ring⟩

theorem UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.lattice_common_denominator :
    ∀ (I : Formalism.MainNotions.S.AutInst),
      ∃ (b : NumberField.RingOfIntegers I.E),
        b ≠ (0 : NumberField.RingOfIntegers I.E) ∧
          ∀ y ∈ I.L, ∀ (i : Fin I.n), ∃ (c : NumberField.RingOfIntegers I.E), (↑c : I.E) = (↑b : I.E) * y i := by
  intro I
  exact UpperTheory.Reformulated.B.LatticeCoordinatesCommonDenominator.denom_of_fg I.L I.L_fg
