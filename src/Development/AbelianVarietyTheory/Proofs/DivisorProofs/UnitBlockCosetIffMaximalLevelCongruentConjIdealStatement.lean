module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetIffMaximalLevelCongruentConjIdeal
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise


theorem _root_.GlobalTheory.T.unitBlockCoset_iff_maximalLevel_congruent_conjIdeal : ∀ {D : D7} (S T : HSp D), S.gram = 1 →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e P →
    ∀ o : ℕ, o + S.rank = T.rank → ∀ k ∈ GlobalTheory.NormSum.intG D S.rank, ∀ k' ∈ GlobalTheory.NormSum.intG D S.rank, ∀ g g' : Formalism.L2.Theta.GA D S,
    GlobalTheory.BotFormula.IsFinPt S g k → GlobalTheory.BotFormula.IsFinPt S g' k' → ∀ y : WO S T,
    cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g⁻¹ 1 y) ≠ 0 →
    (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g'⁻¹ 1 y) ≠ 0 ↔
      CongOne D (D.host.conj • modul P c) (k'⁻¹ * k)) := by
  first | exact @GlobalTheory.BotSmallDict.CosetCong.coset_iff_congOne | exact GlobalTheory.BotSmallDict.CosetCong.coset_iff_congOne | (intros; apply GlobalTheory.BotSmallDict.CosetCong.coset_iff_congOne <;> assumption)
