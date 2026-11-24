module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.ConvInfProof

theorem tendsto_prod_shift (m₀ : Multiset ℂ) {z : ℕ → ℂ} {z₀ : ℂ} (h : Tendsto z atTop (𝓝 z₀)) (u : ℂ) :
    Tendsto (fun k => ((m₀.map (· + z k)).map (u + ·)).prod) atTop
      (𝓝 (((m₀.map (· + z₀)).map (u + ·)).prod)) := by
  induction m₀ using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (tendsto_const_nhds.add (h.const_add a)).mul ih

theorem convInf_of_discInf_topInf : DiscInf → TopInf → ConvInf := by
  intro hD hT E _ _ _ N t s τ hc hs
  induction hc with
  | leaf V z z₀ h =>
    have hex : ∃ m₀, HasInfCharGL V τ m₀ := by
      rcases hs with ⟨rfl, rfl, -⟩ | ⟨-, hV, -⟩
      · exact ⟨0, hT E τ⟩
      · exact hD E _ V hV τ
    obtain ⟨m₀, h₀⟩ := hex
    exact ⟨m₀.map (· + z₀), fun k => m₀.map (· + z k), ⟨m₀, h₀, rfl⟩, fun k => ⟨m₀, h₀, rfl⟩,
      fun u => tendsto_prod_shift m₀ h u⟩
  | node h₁ h₂ ih₁ ih₂ =>
    obtain ⟨a₀, a, ha₀, ha, hat⟩ := ih₁ hs.1
    obtain ⟨b₀, b, hb₀, hb, hbt⟩ := ih₂ hs.2
    refine ⟨a₀ + b₀, fun k => a k + b k, ⟨a₀, b₀, ha₀, hb₀, rfl⟩,
      fun k => ⟨a k, b k, ha k, hb k, rfl⟩, fun u => ?_⟩
    simp only [Multiset.map_add (f := _), Multiset.prod_add]
    exact (hat u).mul (hbt u)

end GlobalTheory.CompanionTheory.EGlue.ConvInfProof

end
