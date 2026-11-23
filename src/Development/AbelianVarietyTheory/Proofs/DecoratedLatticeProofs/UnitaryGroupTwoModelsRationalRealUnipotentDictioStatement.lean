module

public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitaryGroup_twoModels_rationalReal_unipotent_dictionary : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ GQ V ↔ x ∈ (Formalism.IndefR.Eqv.UI.instV fr).GFset) ∧ (∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (τ : D.what₂.Tau) (A : Matrix (Fin V.rank) (Fin V.rank) ℂ), A = uMat (x.1 (Formalism.L2.Host.tauPl D τ)) → infMat D.sp.cm.sig V.gram (θ τ) (Formalism.IndefR.Eqv.UI.brg fr x) = fr.P (Formalism.L2.Host.tauPl D τ) * A * (fr.P (Formalism.L2.Host.tauPl D τ))⁻¹) ∧ ∀ W, (Formalism.IndefR.Eqv.UI.instV fr).IsIsot W → ∃ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ ∧ ∀ x, Formalism.IndefR.Eqv.UI.brg fr x ∈ NI V C₀ → x ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W := by
  first | exact @GlobalTheory.BridgeDict.bridge_dict | exact GlobalTheory.BridgeDict.bridge_dict | (intros; apply GlobalTheory.BridgeDict.bridge_dict <;> assumption)
