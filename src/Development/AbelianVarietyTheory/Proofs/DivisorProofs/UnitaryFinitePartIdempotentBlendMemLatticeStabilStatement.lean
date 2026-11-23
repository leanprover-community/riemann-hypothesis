module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePartIdempotentBlendMemLatticeStabil
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unitaryFinitePart_idempotentBlend_mem_latticeStabilizer : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := by
  first | exact @GlobalTheory.StabMove.finE_mem_St | exact GlobalTheory.StabMove.finE_mem_St | (intros; apply GlobalTheory.StabMove.finE_mem_St <;> assumption)
