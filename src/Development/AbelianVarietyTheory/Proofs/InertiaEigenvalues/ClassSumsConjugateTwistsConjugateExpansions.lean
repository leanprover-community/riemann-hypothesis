module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateThetaSeriesFlatVectorsTwistedWeilStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormLinearRelationDefinedOverCoreField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemGfCOfSuppAtIdem
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

namespace GlobalTheory.PlaceClassSum

theorem classSum_conj_place : ∀ (D : D7) (X : RealSide D) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), B.Good → ∀ ψ ψ' : Twist D Circle, ψ.Good → ψ'.Good → B.admitted ψ.Q →
  GlobalTheory.BigOn.Exp.TwConj.HasTuples X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O (fun _ => 1) j B ψ ψ' →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u → ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc → κ ≠ 0 →
  ∀ τ : ℂ ≃+* ℂ, FixBase X.core X.R.toRealDat j τ → FixDat B τ → ConjChar τ ψ ψ' → ∀ ω ω' : PairRep (Vc D j) (Wc D j), B.IsWeil ψ.chi ω → B.IsWeil ψ'.chi ω' →
  ∃ ζ : ℂ, IsRoot1 ζ ∧ ∀ (I : Type) [Fintype I] (rep : I → GA D (Vc D j)), (∀ a, rep a ∈ GfC (Vc D j)) → ∀ F F' : Amb D j,
    ConjAt (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ τ F F' →
    ConjFun (X.geo.O j) (X.geo.κ j) τ ζ (κ • B.classSum ω ψ rep F) (κ • B.classSum ω' ψ' rep F') := by
  intro D X j B hB ψ ψ' hψ hψ' hadm hT u cc κ hu hc hκ τ hτ hfd hcc ω ω' hω hω'
  obtain ⟨T0', A', R', F', v₀', O', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, t, t', ht, ht'⟩ := hT
  obtain ⟨c', u', hc', hu', hio⟩ := h11 cc u hc hu
  obtain ⟨ζ, hζ, H⟩ := GlobalTheory.T.conjugate_thetaSeries_flatVectors_twistedWeil GlobalTheory.chartIndependence_unconditional D _ _ T0' A' X.core R' F' X.geo.κ v₀' O' (fun _ => 1) X.size
    h1 h2 h3 h4 h5 j h6 h7 c' hc' u' hu' B hB h8 τ (h9 τ hτ) hfd ω ω' ψ ψ' t t' hω hω' hψ hψ' hadm ht ht' hcc
  have hz : GlobalTheory.ConjSpan.RelConj (O' j) (X.geo.κ j) τ :=
    GlobalTheory.ConjRelation.expands_zero_conj D _ _ T0' A' X.core R' F' X.geo.κ v₀' h1 h3 j Unit _ (O' j) h6.2 τ hτ.core
  refine ⟨ζ, hζ, fun I _ rep hrep F F' hF => h10 _ _ _ _ ?_⟩
  have := GlobalTheory.ConjSpan.classSum_conj (R'.ioP j (PiTensorProduct.tprod ℂ u')) c' hz hκ hcc.1 H I rep hrep F F' fun h => by
    obtain ⟨x, x', hx, e, e'⟩ := hF h
    exact ⟨x, x', hx, e.trans (hio x).symm, e'.trans (hio _).symm⟩
  rwa [one_mul] at this

end GlobalTheory.PlaceClassSum
