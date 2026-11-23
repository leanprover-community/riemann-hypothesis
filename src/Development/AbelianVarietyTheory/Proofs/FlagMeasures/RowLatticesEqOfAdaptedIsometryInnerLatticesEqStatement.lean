module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesEqOfAdaptedIsometryInnerLatticesEq
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

theorem _root_.GlobalTheory.T.rowLattices_eq_of_adaptedIsometry_innerLattices_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (v : D.what₂.Word) (B : LFlag (D.sp.Y 0) D.R.rS ((Tu D v : ℕ) : D.host.E)) (ψ₀ ψ₁ : GV D) (Λa Λb : LV D), Λa ∈ Y.what₂ v → Λb ∈ Y.what₂ v → Adapt ψ₀ (lf D (X.Fu v)) B → Adapt ψ₁ (lf D (X.Fu v)) B → Lsub (Formalism.HermitianLatticesTheory.gmap ψ₀ Λa) B = Lsub (Formalism.HermitianLatticesTheory.gmap ψ₁ Λb) B → Λb = Λa ∧ ∃ n ∈ NRat (lf D (X.Fu v)), n * (ψ₁⁻¹ * ψ₀) ∈ Aut0 (lf D (X.Fu v)) Λa := by
  first | exact @GlobalTheory.Unfold.SideEq.side | exact GlobalTheory.Unfold.SideEq.side | (intros; apply GlobalTheory.Unfold.SideEq.side <;> assumption)
