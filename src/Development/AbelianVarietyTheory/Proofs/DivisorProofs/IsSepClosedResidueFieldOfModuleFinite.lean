module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAlgebrasOverHenselianAndComplete
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory

open IsLocalRing

theorem isLocalHom_algebraMap_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T] :
    IsLocalHom (algebraMap R T) := by
  constructor
  intro a ha
  by_contra hna
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI hmax : (Ideal.comap (algebraMap R T) (maximalIdeal T)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal T)
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hm : a ∈ Ideal.comap (algebraMap R T) (maximalIdeal T) := by
    rw [heq]; exact (mem_maximalIdeal a).2 hna
  exact (mem_maximalIdeal _).1 hm ha

theorem isSepClosed_residueField_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing T] [IsLocalRing T] [Algebra R T]
    [Module.Finite R T] : IsSepClosed (ResidueField T) := by
  haveI := isLocalHom_algebraMap_of_moduleFinite R T
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (ResidueField R) (ResidueField T) := inferInstance
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField T) := inferInstance
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)

theorem finite_algebra_strictly_henselian_pi : ∀ (R S : Type) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing S] [Algebra R S] [Module.Finite R S],
    ∃ (ι : Type) (_ : Finite ι) (T : ι → Type) (_ : ∀ i, CommRing (T i))
      (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i) (_ : ∀ i, HenselianLocalRing (T i)),
      ∀ i, IsSepClosed (ResidueField (T i)) ∧ Module.Finite R (T i) := by
  intro R S _ _ _ _ _ _
  obtain ⟨ι, hι, T, hT, hA, e, h⟩ := ((finite_algebras_over_henselian R).1 S).1
  refine ⟨ι, hι, T, hT, hA, e, fun i ↦ (h i).1, fun i ↦ ⟨?_, (h i).2⟩⟩
  haveI := (h i).1
  haveI := (h i).2
  exact isSepClosed_residueField_of_moduleFinite R (T i)

end GlobalTheory
