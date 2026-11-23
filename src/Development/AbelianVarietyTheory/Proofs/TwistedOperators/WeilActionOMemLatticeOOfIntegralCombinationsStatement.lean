module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionOMemLatticeOOfIntegralCombinations
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open Matrix


theorem _root_.GlobalTheory.T.weilActionO_mem_latticeO_of_integralCombinations : ∀ {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T)
    (AS BS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (AT BT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    (∀ s ∈ AS, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin S.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BS) ∧
      ∀ i, finPart D ((mt S g *ᵥ fun k => incA D (s k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    (∀ t ∈ AT, ∃ (m : ℕ) (β : Fin m → Formalism.L2.Theta.AE D) (b : Fin m → Fin T.rank → D.host.E),
      (∀ p, finPart D (β p) ∈ intAE D) ∧ (∀ p, b p ∈ BT) ∧
      ∀ i, finPart D ((mt T h *ᵥ fun k => incA D (t k)) i) =
        finPart D (∑ p, β p * incA D (b p i))) →
    ∀ w ∈ latO S T (AS : Set (Fin S.rank → D.host.E)) (AT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T g h w ∈ latO S T (BS : Set (Fin S.rank → D.host.E)) (BT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  first | exact @GlobalTheory.LatMoveGen.actO_mem_latO | exact GlobalTheory.LatMoveGen.actO_mem_latO | (intros; apply GlobalTheory.LatMoveGen.actO_mem_latO <;> assumption)
