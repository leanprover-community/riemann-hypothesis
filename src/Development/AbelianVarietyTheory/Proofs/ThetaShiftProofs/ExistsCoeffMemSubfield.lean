module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace GlobalTheory.ArcPts

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory Filter
open scoped LaurentSeries PowerSeries

theorem exists_coeff_mem_subfield {k L V ι : Type*} [Field k] [Field L] [Algebra k L] [Fintype ι]
    (K : IntermediateField k L) (r : ι → L) (g : ι → V → L) (f : V → L) (hg : ∀ i v, g i v ∈ K)
    (hf : ∀ v, f v ∈ K) (h : ∀ v, f v = ∑ i, r i * g i v) :
    ∃ s : ι → L, (∀ i, s i ∈ K) ∧ ∀ v, f v = ∑ i, s i * g i v := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap K L).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (algebraMap K L).injective)
  refine ⟨fun i => π (r i), fun i => (π (r i)).2, fun v => ?_⟩
  have h1 : π (f v) = ⟨f v, hf v⟩ := LinearMap.congr_fun hπ ⟨f v, hf v⟩
  have h2 : π (f v) = ∑ i, π (r i) * ⟨g i v, hg i v⟩ := by

    rw [h v, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : r i * g i v = (⟨g i v, hg i v⟩ : K) • r i := by
      rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have h3 := congrArg (fun x : K => (x : L)) (h1.symm.trans h2)
  simpa using h3

theorem exists_isComb_halfRing : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), AnFin A →
    ∀ (j : ℕ) [NeZero j] (f : A.V → ℂ⸨X⸩), IsComb A j Set.univ f → (∀ v, f v ∈ Conv.convLaurent) →
    ∃ T : ℝ, IsComb A j (Conv.halfRing T) f ∧ ∀ v, f v ∈ Conv.halfRing T := by
  rintro O _ _ A - j _ f ⟨n, r, α, th, h1, h2⟩ hf
  obtain ⟨T₀, h₀⟩ := A.exists_isConvLine
  have hm : ∀ i v, A.FSum j (α i) (th i) v ∈ Conv.halfRing T₀ := fun i v _ hw =>
    (AnArc.hasSum_coeff_FSum h₀ (h1 i).2 hw v).summable
  obtain ⟨s, hs, hfs⟩ := exists_coeff_mem_subfield Conv.convLaurent r (fun i v => A.FSum j (α i) (th i) v) f
    (fun i v => Conv.halfRing_le_convLaurent T₀ (hm i v)) hf h2
  obtain ⟨T, hT, hT₀⟩ := ((eventually_all.2 fun i => Conv.eventually_mem_halfRing (hs i)).and
    (eventually_ge_atTop T₀)).exists
  refine ⟨T, ⟨n, s, α, th, fun i => ⟨hT i, (h1 i).2⟩, hfs⟩, fun v => ?_⟩
  rw [hfs v]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hT i) (Conv.halfRing_mono hT₀ (hm i v))

end GlobalTheory.ArcPts
