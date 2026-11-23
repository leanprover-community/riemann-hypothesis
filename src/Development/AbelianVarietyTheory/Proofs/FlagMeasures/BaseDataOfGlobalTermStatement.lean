module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseDataOfGlobalTerm
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

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.baseData_of_global_term : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ w : Point D.host.E (D.R.rS + 1), IsInCell (ZhatOM (ZhatL (lf D F0) F')) w → ∃ (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 F'1 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : ∀ p, LocNG.Datum (FP p)), (∃ n ∈ Formalism.L2.SG.NGData.NRat (lf D F0), ∀ a, frame F00 a = n (frame (lf D F0) a)) ∧ ZhatOM (ZhatL F00 F'0) = ptMat w ∧ Gval F00 F'0 ≠ 0 ∧ IsInCell (ZhatOM (ZhatL (lf D F0) F'1)) w ∧ (∀ p, AtBase Z p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Z.M p)) ∧ LocNG.IsTermOver (FP p) (d0 p) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' = scaled Z p (frame F'1)) ∧ {p : PlF D | ¬ ((FP p).PrimeTo ∧ LocNG.IsTermOver (FP p) (d0 p) ⟨lattice₂ D Z.M p Λ, scaled Z p (frame F00), scaled Z p (frame F'0), ((Tu D u : ℕ) : (D.s.atP p).Fp), ((Tu D u' : ℕ) : (D.s.atP p).Fp)⟩)}.Finite := by
  first | exact @GlobalTheory.BaseTerm.base_data_of_global_term | exact GlobalTheory.BaseTerm.base_data_of_global_term | (intros; apply GlobalTheory.BaseTerm.base_data_of_global_term <;> assumption)
