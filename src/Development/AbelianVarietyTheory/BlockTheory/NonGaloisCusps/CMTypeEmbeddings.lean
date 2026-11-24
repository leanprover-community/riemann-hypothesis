module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.L2.Host NumberField IsDedekindDomain

def hcSigma {R : Ranks} (P : HCParam R) : Multiset ℂ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map (fun i => ((P.v i : ℚ) : ℂ)) +
    (Finset.univ : Finset (Fin R.m)).val.map (fun j => -((P.b j : ℚ) : ℂ))

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := embPsi D.host (D.eTau τ)

def embTauBar (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := (starRingEnd ℂ).comp (embTau D τ)

def IsCuspParam (D : D7) (S : GlobalTheory.HeightCounting.RowSide D) (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop :=
  D.naut.csd π ∧
  D.naut.ralg π ∧
  (∀ w : PlE D.host, IsSplitPl D.host w → D.naut.locG π w = S.locR σ w) ∧
  (∀ w : PlE D.host, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG π w)) ∧
  (∀ w : PlE D.host, IsSplitPl D.host w → (∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
    D.naut.unr (D.naut.locG π w)) ∧
  (∀ τ : D.what₂.Tau, D.naut.infG π (embTau D τ) = hcSigma (D.hc τ) ∧
    D.naut.infG π (embTauBar D τ) = (hcSigma (D.hc τ)).map (fun z => -z))

def GoodRowCuspParam (D : D7) (S : GlobalTheory.HeightCounting.RowSide D) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ σ : D.what₂.FT, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ →
    ∃ π : D.naut.CG D.R.r, IsCuspParam D S σ π

theorem hcSigma_int {R : Ranks} (P : HCParam R) : ∀ z ∈ hcSigma P, ∃ n : ℤ, z = (n : ℂ) := by
  intro z hz
  simp only [hcSigma, Multiset.mem_add, Multiset.mem_map] at hz
  rcases hz with ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩
  · obtain ⟨n, hn⟩ := P.v_int i
    exact ⟨n, by rw [hn]; simp⟩
  · obtain ⟨n, hn⟩ := P.b_int j
    exact ⟨-n, by rw [hn]; simp⟩

theorem IsCuspParam.unr {D : D7} {S : GlobalTheory.HeightCounting.RowSide D} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
    (h : IsCuspParam D S σ π) (w : PlE D.host) (hw : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) :
    D.naut.unr (D.naut.locG π w) := by
  by_cases hs : IsSplitPl D.host w
  · exact h.2.2.2.2.1 w hs hw
  · exact h.2.2.2.1 w hs

end GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

end
