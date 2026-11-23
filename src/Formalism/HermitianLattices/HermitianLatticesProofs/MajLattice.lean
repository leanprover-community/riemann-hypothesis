module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonMajorizingLattice
public import Lemmata.GeneralBFactSecondRest.Imports
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic

@[expose] public section

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix

noncomputable section

namespace Formalism.HermitianLatticesTheory

section MajLatticeAux

variable {K : Type*} [Field K] [NumberField K]

theorem majLattice_common (t : Finset K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ t, IsIntegral ℤ ((d : K) * a) := by
  first | exact UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common .. | (apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› t | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K

end MajLatticeAux

section MajLatticeMain

variable {K V ι : Type*} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem majLattice_exists_c (L : Submodule (𝓞 K) V)
    (hL : Submodule.span K (L : Set V) = ⊤) (y : V) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ L := by
  first | exact Bl.general_b_fact_second_rest.goal1 .. | (apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second_rest.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_rest.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL y | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L hL | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› L | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V ‹_› | exact @Bl.general_b_fact_second_rest.goal1 K V | exact @Bl.general_b_fact_second_rest.goal1 K

theorem majLattice_exists_d (b : Basis ι K V) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((d : K) * b.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  obtain ⟨d, hd, ht⟩ := majLattice_common (s.biUnion fun g => Finset.univ.image fun i => b.repr g i)
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    intro i
    exact ht _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  | zero => intro i; simpa using isIntegral_zero
  | add x y _ _ hx hy =>
    intro i
    simp only [map_add (f := _), Finsupp.add_apply, mul_add]
    exact (hx i).add (hy i)
  | smul r x _ hx =>
    intro i
    have : b.repr (r • x) i = algebraMap (𝓞 K) K r * b.repr x i := by
      rw [← algebraMap_smul K r x, map_smul]; rfl
    rw [this, mul_left_comm]
    exact (RingOfIntegers.isIntegral_coe r).mul (hx i)

end MajLatticeMain

end Formalism.HermitianLatticesTheory
