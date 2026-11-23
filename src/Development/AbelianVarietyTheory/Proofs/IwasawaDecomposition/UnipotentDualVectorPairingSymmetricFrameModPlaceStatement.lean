module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipotentDualVectorPairingSymmetricFrameModPlace
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentDualVector_pairing_symmetricFrame_mod_place : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (k : Fin 2), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal → GlobalTheory.Mem.SymFrame.EwAt X w → 1 - X.ew ∈ GlobalTheory.Mem.SymChar.wInt X w → ∀ (i : Fin D.R.k) (j : Fin D.R.r), hA X.B.I (X.bwd i) (GlobalTheory.Mem.SymFrame.symVec X w j) - (if j = GlobalTheory.Mem.SymChar.Resid.posB D i then 1 else 0) ∈ GlobalTheory.Mem.SymChar.wInt X w := by
  first | exact @GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec | exact GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec | (intros; apply GlobalTheory.Mem.SymChar.Resid.hA_bwd_symVec <;> assumption)
