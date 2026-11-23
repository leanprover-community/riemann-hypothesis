module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.EvalFam
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.LeMCoordIdealOfTorus
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
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder


theorem _root_.GlobalTheory.CompanionTheory.Relay.lowerBound_height_on_boundary : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω] (x : (Σ k, J k) → Ω) (n : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel x n bd → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal x) (n + 1) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal x) ∩ mcPts bd) : Set (mcPts (mCoordIdeal x))) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → GroundTheory.Heights₂.Heights.LowerBoundFree.torusSmul c z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → (∀ z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd, GroundTheory.Heights₂.Heights.LowerBoundFree.conjVec z ∈ mcPts (mCoordIdeal x) ∩ mcPts bd) → ∃ (Rb : AnLogRes (mCoordIdeal x) ⊤ n) (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set Rb.X), IsPotential Rb.A L ∧ IsSection Rb.A L s ∧ IsSNC Rb.A L s m W ∧ (∀ p, logNormSec L s p ≤ 0) ∧ (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ mcPts bd) ∧ ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → rW L s p' = rW L s p := by
  intro K _ J _ Ω _ _ x n bd hsnc harith _ htor hconj
  obtain ⟨I, hIh, hIle, hIsnc, hIeq⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_homogIdeal x n bd hsnc harith htor
  obtain ⟨Rb, nb, W, hloc⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.exists_res x n I harith hIh hIle hIsnc
  rw [hIeq] at hloc
  obtain ⟨L, s, h1, h2, h3, h4, h5, h6⟩ :=
    PositivityTheory.Xgp.c_bm_exists_boundary.assemble Rb (mcPts (mCoordIdeal x) ∩ mcPts bd)
      (fun z hz c hc => htor z hz c hc) (fun z hz => hconj z hz) nb W hloc
  refine ⟨Rb, L, s, nb, fun _ => 1, W, h1, h2, h3, h4, fun p => ?_, h6⟩
  rw [h5 p]
  exact ⟨fun hp => hp.2, fun hp => ⟨Rb.mem p p (Rb.mem_U p), hp⟩⟩
