module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne

@[expose] public section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

theorem basV_repr_mul (G : HTGroup p) (v : AwayP p) (a b : Qv v ⊗[ℚ] G.C) (k : Fin (Module.finrank ℚ G.C)) :
    (basV G v).repr (a * b) k = ∑ i, ∑ j, (basV G v).repr a i * (basV G v).repr b j *
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) := by
  conv_lhs => rw [← (basV G v).sum_repr a, ← (basV G v).sum_repr b]

  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul, map_sum, map_smul, Finset.sum_apply',
  Finsupp.smul_apply, smul_eq_mul, basV, Algebra.TensorProduct.basis_apply,
  Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul,
  Finsupp.mapRange_apply]
  rw [Finset.sum_comm]


omit [Fact p.Prime] in
theorem eventually_rat_mem_integers (q : ℚ) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      algebraMap ℚ (Qv v) q ∈ v.1.adicCompletionIntegers ℚ := by
  have h : ∀ᶠ w in (Filter.cofinite : Filter (HeightOneSpectrum ℤ)),
      algebraMap ℚ (w.adicCompletion ℚ) q ∈ w.adicCompletionIntegers ℚ :=
    (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q).2
  exact Subtype.val_injective.tendsto_cofinite.eventually h

theorem isIntV_mul_eventually (G : HTGroup p) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) := by
  have h : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ i j k : Fin (Module.finrank ℚ G.C),
      algebraMap ℚ (Qv v) ((Module.finBasis ℚ G.C).repr
        (Module.finBasis ℚ G.C i * Module.finBasis ℚ G.C j) k) ∈ v.1.adicCompletionIntegers ℚ := by
    simp only [Filter.eventually_all]
    intro i j k
    exact eventually_rat_mem_integers _
  filter_upwards [h] with v hv a b ha hb k
  rw [basV_repr_mul]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
    Subring.mul_mem _ (Subring.mul_mem _ (ha i) (hb j)) (hv i j k)

theorem isIntV_mul_eventually' : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p),
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∀ a b : Qv v ⊗[ℚ] G.C,
      IsIntV G v a → IsIntV G v b → IsIntV G v (a * b) :=
  fun _ _ G => isIntV_mul_eventually G

end GlobalTheory.OrbFinAf
