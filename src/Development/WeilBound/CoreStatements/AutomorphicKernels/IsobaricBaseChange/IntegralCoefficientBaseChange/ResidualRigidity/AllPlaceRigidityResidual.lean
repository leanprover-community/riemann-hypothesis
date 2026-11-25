module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.StringsTwo
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec

namespace GlobalTheory.Rigid

theorem strings_eq_map {X ι : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) :
    strings p d = ∑ x : (Σ i, Fin (d i)), ({(p x.1, spehExp (d x.1) x.2)} : Multiset (X × ℝ)) := by
  unfold strings
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_multiset_sum]
  exact (Multiset.sum_map_singleton _).symm.trans (by rw [Multiset.map_map]; rfl)

theorem strings_eq_of_equiv {X ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → X) (d : ι → ℕ) (p' : κ → X) (d' : κ → ℕ)
    (s : (Σ i, Fin (d i)) ≃ (Σ j, Fin (d' j)))
    (hs : ∀ x, p x.1 = p' (s x).1 ∧ spehExp (d x.1) x.2 = spehExp (d' (s x).1) (s x).2) :
    strings p d = strings p' d' := by
  rw [strings_eq_map, strings_eq_map]
  refine Fintype.sum_equiv s _ _ fun x => ?_
  rw [(hs x).1, (hs x).2]

end GlobalTheory.Rigid
