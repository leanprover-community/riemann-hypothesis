module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Order.SupIndep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DisjointFinsetSupOfSupIndepSup
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


theorem _root_.GlobalTheory.T.disjoint_finset_sup_of_supIndep_sup' : ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → Disjoint (F.sup G) (F.sup B) := by
  first | exact @GlobalTheory.disjoint_finset_sup_of_supIndep_sup | exact GlobalTheory.disjoint_finset_sup_of_supIndep_sup | (intros; apply GlobalTheory.disjoint_finset_sup_of_supIndep_sup <;> assumption)
