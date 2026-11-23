module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicSumEqOfFramesInnerConj
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.isotypicSum_eq_of_frames_innerConj : ∀ {D : D7} (Y W : HSp D) {n : ℕ} (PY : principalLevelFrame.RowPsi Y n) (PW : principalLevelFrame.RowPsi W n) (Φ : GfC Y ≃ₜ* GfC W) (h : Formalism.AUTREP.GAf D.host.E n), (∀ κ, ((Φ ⟨PY.ψ κ, PY.into κ⟩ : GfC W) : GA D W) = PW.ψ (h * κ * h⁻¹)) → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (GfC W) X) (C : Submodule ℂ X) (π : Formalism.L2.NG.FinTyp D.host.E n), (⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PY).symm.toMonoidHom) (ρ.comp Φ.toMulEquiv.toMonoidHom) C, LinearMap.range f) = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv PW).symm.toMonoidHom) ρ C, LinearMap.range f := by
  first | exact @GlobalTheory.FrameIsot.iSup_homInto_frame_conj | exact GlobalTheory.FrameIsot.iSup_homInto_frame_conj | (intros; apply GlobalTheory.FrameIsot.iSup_homInto_frame_conj <;> assumption)
