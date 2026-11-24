module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.OreLocalization.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenIsUnitOfNotMemMap
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.exists_basicOpen_isUnit_of_notMem_map' : ∀ (S : Type) [CommRing S] (f₀ : S) (q : Ideal S), q.IsPrime → f₀ ∉ q → ∀ (J : Type) [Finite J] (m : J → Localization.Away f₀), (∀ i, m i ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q) → ∃ f : S, f ∉ q ∧ ∃ φ : Localization.Away f₀ →ₐ[S] Localization.Away f, ∀ i, IsUnit (φ (m i)) := by
  first | exact @GlobalTheory.exists_basicOpen_isUnit_of_notMem_map | exact GlobalTheory.exists_basicOpen_isUnit_of_notMem_map | (intros; apply GlobalTheory.exists_basicOpen_isUnit_of_notMem_map <;> assumption)
