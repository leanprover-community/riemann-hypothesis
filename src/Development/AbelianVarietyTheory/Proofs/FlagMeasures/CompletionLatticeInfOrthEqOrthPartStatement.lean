module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletionLatticeInfOrthEqOrthPart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.completion_lattice_inf_orth_eq_orth_part : ∀ (D : D7) (Z : LocDat D) (U : Submodule D.host.E (VS D).V), (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) → (∀ (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → ∀ (p : PlF D) (t : Vp D p), t ∈ lattice₂ D Z.M p Λ → (∀ u ∈ U, LocFacts₂ Z.M p t (baseChange₂ D p u) = 0) → t ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) (orth (VS D) U)) := by
  first | exact @GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal | exact GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal | (intros; apply GlobalTheory.Unfold.OrthLoc.mem_localLattice_inf_orthogonal <;> assumption)
