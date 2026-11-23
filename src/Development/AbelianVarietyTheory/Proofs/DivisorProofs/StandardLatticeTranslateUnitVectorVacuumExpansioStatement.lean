module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeTranslateUnitVectorVacuumExpansio
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)


theorem _root_.GlobalTheory.T.standardLattice_translate_unitVector_vacuum_expansion : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ x ∈ (La0 D (tor0 D ⊤ δ) a d), Wd D (tor0 D ⊤ δ) x (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = fun z => ((Real.sqrt (((La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))).index : ℝ))⁻¹ : ℂ) * ∑ᶠ q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) ⧸ (La0 D (tor0 D ⊤ δ) a d).addSubgroupOf (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), Formalism.MainNotions.TaylorLogMetric.kap D (tor0 D ⊤ δ) x ((Quotient.out q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) : VC D a d) * Wd D (tor0 D ⊤ δ) ((Quotient.out q : (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d))) : VC D a d) e0 z := by
  first | exact @GlobalTheory.FunObj.TransExp.wd_iop_expand | exact GlobalTheory.FunObj.TransExp.wd_iop_expand | (intros; apply GlobalTheory.FunObj.TransExp.wd_iop_expand <;> assumption)
