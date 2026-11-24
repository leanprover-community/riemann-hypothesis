module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly
public import GroundTheory.AutomorphicForms.SmoothRep
public import GroundTheory.AutomorphicForms.JacquetAdmissible
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.PfBern.Props1

open PositivityTheory.PfBern.Assembly

section Bridge

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]


omit [TopologicalSpace G] in
theorem fixed_eq_fixedVectors (ρ : Representation ℂ G V) (K : Subgroup G) :
    GlobalTheory.PRep.fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
  ext v
  change (∀ h : K, ρ h v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ ∀ h ∈ K, ρ h v = v
  simp

theorem isSmooth_found_iff (ρ : Representation ℂ G V) :
    GroundTheory.Automorphic.IsSmooth ρ ↔ GlobalTheory.PRep.IsSmooth ρ := Iff.rfl

theorem isAdmissible_of_found {ρ : Representation ℂ G V} (h : GroundTheory.Automorphic.IsAdmissible ρ) :
    GlobalTheory.PRep.IsAdmissible ρ := by
  refine ⟨(isSmooth_found_iff ρ).1 h.1, fun K hKo hKc => ?_⟩
  rw [fixed_eq_fixedVectors]
  exact h.2 K hKc hKo

end Bridge

theorem irrSmoothAdmissible_holds : IrrSmoothAdmissible := by
  intro k _ _ _ _ N X _ _ π hs hi
  have : π.IsIrreducible := hi
  exact isAdmissible_of_found
    (GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible ((isSmooth_found_iff π).2 hs))

end PositivityTheory.PfBern.Props1
