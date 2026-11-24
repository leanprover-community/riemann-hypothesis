module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import GroundTheory.AutomorphicForms.SatakeNormalized
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedInPrincipalSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical


theorem _root_.GlobalTheory.T.induced_in_principal_series : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)), (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) := by
  first | exact @GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace | exact GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace | (intros; apply GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace <;> assumption)
