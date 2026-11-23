module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.IndefiniteReal.TensCastR
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFixedPlaceConjugatorLiftsActByReductions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.exists_fixed_place_conjugator_lifts_act_by_reductions : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ s s' : ReciprocityTheory.Aut.SplitPlace D.host.E, s.w = s'.w → s = s') → ∃ (c : GAf D.host.E D.R.r) (fr : ∀ (k : Fin 2) (v : D.nd.PlG k), GlobalTheory.RowLev.PlFrame X.B.I D.R.r (D.host.g k) (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw k v))), ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 → ∀ (x : GAf D.host.E D.R.r) (γ : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), IsLift s x γ → (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 ∈ X.B.I.Kset ∧ (fr kv.1 kv.2).ActsAs (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 (γ : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) ∧ ∀ kv' : Σ k : Fin 2, D.nd.PlG k, kv' ≠ kv → (fr kv'.1 kv'.2).ActsAs (Formalism.L2.SG.RowsJoinPinned.iotaX X h (MulAut.conj t (PY.ψ (c * x * c⁻¹)))).2 1 := by
  first | exact @GlobalTheory.FixedConj.exists_conj_frames | exact GlobalTheory.FixedConj.exists_conj_frames | (intros; apply GlobalTheory.FixedConj.exists_conj_frames <;> assumption)
