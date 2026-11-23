module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsDedekindDomain NumberField IsLocalRing

namespace GlobalTheory.BinaryUnitForm

theorem exists_eq_of_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] [Finite (ResidueField R)] (t n u : R)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : R, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  obtain ⟨r, s, hrs⟩ := GlobalTheory.UnramifiedHermitian.exists_binary_eq_of_finite
    (a := residue R t) (n := residue R n)
    (by simpa only [map_sub, map_mul, map_pow, map_ofNat] using (hD.map (residue R)).ne_zero)
    (residue R u)
  obtain ⟨r, rfl⟩ := residue_surjective r
  obtain ⟨s, rfl⟩ := residue_surjective s
  have hN : residue R (r ^ 2 + t * r * s + n * s ^ 2) = residue R u := by
    simpa only [map_add (f := _), map_mul, map_pow] using hrs
  have hNu : IsUnit (r ^ 2 + t * r * s + n * s ^ 2) := by
    rw [← residue_ne_zero_iff_isUnit, hN]
    exact (hu.map _).ne_zero
  obtain ⟨w, hw⟩ := hNu.exists_right_inv
  have he : u * w - 1 ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, ← hN, ← map_mul, hw, map_one, sub_self]

  have hspan : Ideal.span {(2 : R), t} = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _ _ hD
    rw [Ideal.mem_span_pair]
    exact ⟨-2 * n, t, by ring⟩
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1
    (show (1 : R) ∈ Ideal.span {(2 : R), t} by rw [hspan]; exact Submodule.mem_top)
  obtain ⟨T, hT⟩ := GlobalTheory.UnramifiedHermitian.exists_add_mul_sq_eq (maximalIdeal R)
    (α ^ 2 + t * α * β + n * β ^ 2) he
  refine ⟨r * (1 + T * α) - n * s * (T * β), r * (T * β) + (1 + T * α) * s + t * s * (T * β), ?_⟩
  linear_combination (r ^ 2 + t * r * s + n * s ^ 2) * T * hαβ
    + (r ^ 2 + t * r * s + n * s ^ 2) * hT + u * hw

theorem exists_eq_adicCompletionIntegers : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F),
    IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F,
      r ^ 2 + t * r * s + n * s ^ 2 = u := by
  intro F _ _ v t n u hD hu
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  exact exists_eq_of_henselian t n u hD hu

end GlobalTheory.BinaryUnitForm
