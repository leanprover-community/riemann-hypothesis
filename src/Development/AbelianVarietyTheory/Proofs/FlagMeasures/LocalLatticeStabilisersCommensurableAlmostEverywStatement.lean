module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeStabilisersCommensurableAlmostEveryw
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

theorem _root_.GlobalTheory.T.localLatticeStabilisers_commensurable_almostEverywhere : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → (∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d) → ∀ (Λ₀ : LV D) (d0 : Dat Z FP), LocOver Λ₀ d0 → (∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ≠ 0 ∧ ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0) ∧ {p | (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype ≠ MulAction.stabilizer ↥(FP p).UW0 (d0 p)}.Finite ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → ∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d p)) ≠ 0 ∧ (MulAction.stabilizer ↥(FP p).UW0 (d p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0 ∧ GlobalTheory.HL.invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) = LocNG.Datum.wt (d0 p) (d p) := by
  first | exact @GlobalTheory.Unfold.LocStab.local_stabilisers | exact GlobalTheory.Unfold.LocStab.local_stabilisers | (intros; apply GlobalTheory.Unfold.LocStab.local_stabilisers <;> assumption)
