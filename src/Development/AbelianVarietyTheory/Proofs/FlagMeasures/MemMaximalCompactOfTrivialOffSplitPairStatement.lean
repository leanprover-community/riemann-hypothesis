module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfTrivialOffSplitPair
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
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

theorem _root_.GlobalTheory.T.mem_maximalCompact_of_trivial_off_splitPair : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), ε * ε = ε → ε * Formalism.L2.SG.HidaSetting.sigA I ε = 0 → ε ∈ Formalism.MainNotions.S.IntAf I.F I.E → ∀ (k : I.Gf), (∀ i j, (1 - ε - Formalism.L2.SG.HidaSetting.sigA I ε) * (I.fmat k - 1) i j = 0) → (∀ i j, ε * ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (∀ i j, ε * ((β₀⁻¹ * ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → k ∈ I.Kset := by
  first | exact @GlobalTheory.SplitPairK.mem_kset_of_split | exact GlobalTheory.SplitPairK.mem_kset_of_split | (intros; apply GlobalTheory.SplitPairK.mem_kset_of_split <;> assumption)
