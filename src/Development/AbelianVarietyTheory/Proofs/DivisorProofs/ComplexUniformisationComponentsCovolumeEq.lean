module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLevelGroupDataSameCovolumeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportSelfDualDataOneHermitianSpaceStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField

namespace GlobalTheory.EqCovol

theorem covol_eq_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k k' : U.Comp, GlobalTheory.TrueCx.covol (U.X k) = GlobalTheory.TrueCx.covol (U.X k') := by
  intro E _ _ _ H Dw l Xo c σ r U hσ hU hG hp hq k k'
  obtain ⟨Y, hΨ, hp0, -, -, -, hL, hS, hc⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k
  obtain ⟨Y', hΨ', hp0', -, -, -, hL', hS', hc'⟩ := GlobalTheory.T.exists_fullLevelGroup_data_same_covolume E H Dw l Xo c σ r U hσ hU hG hp hq k'
  obtain ⟨hr, hk, -⟩ := hU
  have hY : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ ▸ (hk k).2 τ
  have hY' : ∀ τ : E →+* ℂ, τ ∈ Y'.Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => hΨ' ▸ (hk k').2 τ
  have eΨ : Y'.Ψ = Y.Ψ := Finset.ext fun τ => (hY' τ).trans (hY τ).symm
  have ep : Y'.p0 = Y.p0 := by rw [hp0, hp0', (hk k).1, (hk k').1]
  have h1 : 1 ≤ Y.p0 := by rw [hp0, (hk k).1]; exact hq
  have h2 : Y.p0 < r := by rw [hp0, (hk k).1, hr]; omega
  obtain ⟨Z, hZΨ, hZG, hZξ, hZp, hZL, hZS, hZc⟩ := GlobalTheory.T.exists_transport_selfDual_data_one_hermitianSpace E H l r Y Y' hY eΨ ep h1 h2 hL' hS hS'
  rw [hc, hc', ← hZc]
  exact GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space E H l r Y Z hG hY hZΨ hZG hZξ hZp h1 h2 hL hZL hS hZS

end GlobalTheory.EqCovol
