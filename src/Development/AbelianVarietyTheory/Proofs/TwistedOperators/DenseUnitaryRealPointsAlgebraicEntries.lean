module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RealAlgDense

theorem dense_alg : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ V : HSp D, Dense {g : GinfC V | ∀ τ a b, IsAlgebraic ℚ (compAt θ τ (Formalism.L2.Theta.mt V g.1) a b)} := by
  intro D θ hθ V
  obtain ⟨e, he⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have hfin : ∀ h : GA D V, h ∈ GinfC V ↔ (e h).2 = 1 := fun h =>
    ⟨fun H => Subtype.ext (Units.ext ((he h).1.trans (congrArg Units.val (MonoidHom.mem_ker.1 H)))),
      fun H => MonoidHom.mem_ker.2 (Units.ext ((he h).1.symm.trans (by rw [H]; rfl)))⟩
  have hne : ∃ z, D.sp.cm.sig z ≠ z := by
    by_contra h
    push Not at h
    have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun z => (D.sp.cm.fixed z).1 (h z)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap D.host.F D.host.E).injective, hs⟩
    have h2 := D.sp.cm.deg2
    omega
  have hd := GlobalTheory.RealApprox.dense_inf D.host.F D.host.E D.sp.cm.sig (fun x => star_star x) hne V.gram
    (GlobalTheory.AutFunCounterexample.gram_herm V) (GlobalTheory.AutFunCounterexample.gram_det_ne V)
  let Φ : HA (Ainf D.host.F) D.sp.cm.sig V.gram → GinfC V := fun x =>
    ⟨e.symm (x, 1), (hfin _).2 (by rw [e.apply_symm_apply])⟩
  have hΦc : Continuous Φ :=
    Continuous.subtype_mk (e.symm.continuous.comp (continuous_id.prodMk continuous_const)) _
  have hΦs : Function.Surjective Φ := by
    intro g
    refine ⟨(e g.1).1, Subtype.ext ?_⟩
    change e.symm ((e g.1).1, 1) = g.1
    rw [← (hfin g.1).1 g.2]
    exact e.symm_apply_apply g.1
  refine Dense.mono ?_ (hΦs.denseRange.dense_image hΦc hd)
  rintro _ ⟨x, ⟨γ₀, hγ₀, hx⟩, rfl⟩ τ a b
  have hm := (he (e.symm (x, 1))).2
  rw [e.apply_symm_apply] at hm
  have key : compAt θ τ (Formalism.L2.Theta.mt V (Φ x).1) a b = tauE D τ (γ₀.1 a b) := by
    change infMat D.sp.cm.sig V.gram (θ τ) (e.symm (x, 1)) a b = _
    unfold infMat
    rw [← hm, ← hx]
    exact (hθ τ).1 _
  rw [key]
  have h0 : IsAlgebraic ℚ (γ₀.1 a b) := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (γ₀.1 a b)
  first
    | exact h0.algHom (tauE D τ).toRatAlgHom
    | exact IsAlgebraic.map (tauE D τ).toRatAlgHom h0
    | exact (isAlgebraic_algHom_iff (tauE D τ).toRatAlgHom (tauE D τ).injective).2 h0

end GlobalTheory.RealAlgDense
