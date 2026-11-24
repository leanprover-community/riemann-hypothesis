module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfDualWeylTensorReductionEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb


theorem _root_.GlobalTheory.T.mem_smul_top_of_dualWeylTensorReduction_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange → ∀ y : NablaT O N mu, redT O N mu ϖ y = 0 → y ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu)) := by
  first | exact @GlobalTheory.HighWtEmb.mem_smul_top_of_redT_eq_zero | exact GlobalTheory.HighWtEmb.mem_smul_top_of_redT_eq_zero | (intros; apply GlobalTheory.HighWtEmb.mem_smul_top_of_redT_eq_zero <;> assumption)
