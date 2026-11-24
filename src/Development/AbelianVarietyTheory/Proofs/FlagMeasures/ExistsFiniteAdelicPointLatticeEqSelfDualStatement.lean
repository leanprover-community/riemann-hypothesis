module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDual
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)), Submodule.IsLattice I.E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, Formalism.UG.hform (starRingEnd I.E) I.J y x ∈ (algebraMap (𝓞 I.E) I.E).range) → ∃ xf : I.Gf, lamX I (1, xf) = Λ := by
  first | exact @GlobalTheory.SelfDualPoint.exists_lamX_eq | exact GlobalTheory.SelfDualPoint.exists_lamX_eq | (intros; apply GlobalTheory.SelfDualPoint.exists_lamX_eq <;> assumption)
