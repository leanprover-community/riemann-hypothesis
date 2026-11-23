module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import CompanionTheory.AutomorphicTheory.LocalBesselUniqueness.BesselModels.MultiplicityOneUnitaryBranchingOfGapHyp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColDictCoreHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinXOfDecay
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FullExistsOfLocTied
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

section
noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.ColDict
open GlobalTheory.St.SpectralData
namespace UpperTheory.Lit
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem exists_spectralData_gap_alt : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (Y : Formalism.L2.SG.Full.Full X) (hF : FinX Y) (tr : ∀ u, Transport X u (F u)), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D ∧ (∀ x : X.B.I.E, HEq (X.ιE x) x) ∧ X.MeasTie hb ∧ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ ∧ Formalism.L2.SG.LocVol.IsStdChar ψ ∧ Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ ∧ (∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ u, LevelMatch X (tr u) Y.hK ∧ ColDictInto X (tr u) Y.hK ∧ ColDictBij X (tr u) Y.hK ∧ ColDictIsom X (tr u) Y.hK (Y.cs u) (hF.shInj u) := by
  intro hSW hRF D F hG hLT
  obtain ⟨X, hb, ψ, hI, hι, hM, hψ, hstd, hCm, hL, hT⟩ := exists_setting hSW D F hG
  obtain ⟨Y⟩ := GlobalTheory.fullExists_of_locTied D X hLT
  obtain ⟨hWD, hph⟩ := CompanionTheory.Lime.BM.wuDecayOfGap_holds' D hG X
  have hF : FinX Y := GlobalTheory.FinitenessBundle.finX_of_decay hRF D X Y hWD hph
  choose tr htr using hT Y.hK
  refine ⟨X, hb, ψ, Y, hF, tr, hI, hι, hM, hψ, hstd, hCm, hL, hph, fun u => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.St.colDictCore_holds D X u (F u) (tr u) Y.hK (htr u)
    (GlobalTheory.columnLevel_stabTriv D X Y.hK u)
  exact ⟨htr u, h1, h2, h3 _ (Y.cs u) (hF.shInj u) (Y.colReps u)⟩
end UpperTheory.Lit
end
end
