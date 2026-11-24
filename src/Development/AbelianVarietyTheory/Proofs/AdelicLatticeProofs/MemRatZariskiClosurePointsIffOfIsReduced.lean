module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem mem_pts_zeroSet_of_isReduced :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R]
      [Algebra ℚ R] (y : Matrix ι ι R),
      (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧
      (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  intro ι _ _ S' R _ _ y
  refine ⟨fun hy f hf => hy f (fun g hg => hg f hf), fun hR hy f hf => ?_⟩
  have hrad : f ∈ (Ideal.span S').radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hx' := MvPolynomial.mem_zeroLocus_iff.1 hx
    exact hf (Matrix.of fun i j => x (i, j)) (fun p hp => hx' p (Ideal.subset_span hp))
  obtain ⟨n, hn⟩ := hrad
  have hle : Ideal.span S' ≤
      RingHom.ker (MvPolynomial.aeval (R := ℚ) (fun ij : ι × ι => y ij.1 ij.2)) :=
    Ideal.span_le.2 fun p hp => hy p hp
  have h0 := hle hn
  rw [RingHom.mem_ker, map_pow] at h0
  exact IsReduced.eq_zero _ ⟨n, h0⟩

end GlobalTheory.ClassFin
