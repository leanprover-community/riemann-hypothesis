module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusMassEqSumOverRationalGroupOrbits
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  first | exact @GlobalTheory.Unfold.massA_eq_sum_orbits | exact GlobalTheory.Unfold.massA_eq_sum_orbits | (intros; apply GlobalTheory.Unfold.massA_eq_sum_orbits <;> assumption)
