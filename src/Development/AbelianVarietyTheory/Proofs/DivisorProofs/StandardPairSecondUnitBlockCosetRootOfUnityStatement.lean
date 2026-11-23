module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondUnitBlockCosetRootOfUnity
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree

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


theorem _root_.GlobalTheory.T.standardPairSecond_unitBlockCoset_rootOfUnity : ∀ {D : D7} (S T : HSp D), S.gram = 1 → T.gram = 1 → D.host.ccK = ⊤ →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (Formalism.L2.Col.stdLat D.host.E S.rank) →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    ∀ o : ℕ, o + S.rank = T.rank → (∀ w ∈ P, 1 ≤ c w) →
    ∀ (ν : (Formalism.L2.Theta.AE D)ˣ →* Circle) (νH : Formalism.L2.Host.HChar D.host.E), ChrEq ν νH → (∀ w ∈ P, GlobalTheory.CMVal.ExpAt νH w (c w)) →
    ∃ ζ : ℂ, IsRootOne ζ ∧ ∀ y : WO S T, cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) y ≠ 0 →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e (modul P c) o S T βS 1 y = ζ := by
  first | exact @GlobalTheory.BotCosetValue.stdSnd_coset_value | exact GlobalTheory.BotCosetValue.stdSnd_coset_value | (intros; apply GlobalTheory.BotCosetValue.stdSnd_coset_value <;> assumption)
