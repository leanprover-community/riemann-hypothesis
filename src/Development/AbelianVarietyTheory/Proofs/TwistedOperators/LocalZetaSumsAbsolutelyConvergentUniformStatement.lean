module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalZetaSumsAbsolutelyConvergentUniform
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.localZetaSums_absolutely_convergent_uniform : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ), (∀ w, ‖(z w : ℂ)‖ = 1) → ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (φ : ∀ v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}, Gv V v.1 → ℂ), (∀ v, IsLocKer V D.R.nV z v.1 (φ v)) → ∃ A : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} → ℝ, Summable (fun v => A v - 1) ∧ ∀ v, HasSum (fun a : Gv V v.1 ⧸ Kv V v.1 => ‖φ v a.out‖) (A v) := by
  first | exact @GlobalTheory.FinZeta.AbsConv.absConv_localZeta | exact GlobalTheory.FinZeta.AbsConv.absConv_localZeta | (intros; apply GlobalTheory.FinZeta.AbsConv.absConv_localZeta <;> assumption)
