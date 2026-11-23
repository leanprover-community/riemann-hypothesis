module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountConstantEqUnscaledMainConstant
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.meanCountConstant_eq_unscaledMainConstant : PI.VolStabS.MassDataS.SWXS → ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → 2 * D.R.rS + 2 + D.R.f + 5 ≤ D.R.k → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (gS D) ^ 2] → ∀ (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ), MassDataTie X hb X0 ψ → ∀ (sd C Th : ℝ) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf), 0 < Formalism.L2.SG.MassDataConc.ngFac D ∧ Formalism.L2.SG.Pf.Cnt.cExpl D (X.Fu u) (Y.what₂ u) * Formalism.MainNotions.S.Cnt.massRows D (X.Fu u) (Y.what₂ u) * ∏' p, Formalism.L2.SG.DataInst.alpD u u' p = (bkU X hb Y u u' X0 ψ sd C Th vR Q i0 i0' νq).AA * Formalism.L2.SG.MassDataConc.ngFac D := by
  first | exact @GlobalTheory.CountConst.countConst_eq_unscaledConst | exact GlobalTheory.CountConst.countConst_eq_unscaledConst | (intros; apply GlobalTheory.CountConst.countConst_eq_unscaledConst <;> assumption)
