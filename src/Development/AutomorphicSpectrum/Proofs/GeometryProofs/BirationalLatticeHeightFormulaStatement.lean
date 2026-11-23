module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalLatticeHeightFormula
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.birational_lattice_height_formula : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (X : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (e₀ : E) (c₀ : Ω) (A : HermLine ι) (r : HeightOneSpectrum (𝓞 F) →₀ ℚ) (cinf : (F →+* ℂ) → ℝ), OverInt y φ → Birational y → IsConjInvariantH A → CoordTie ℤ ξ (fun c' : (k : K) → ι k => ∏ k, y ⟨k, c' k⟩) → NormalCpt ξ → L.IsDegOn Set.univ y A.a e₀ → c₀ ≠ 0 → (∀ p : Cpt ξ, ((∀ a : F, φ a ∈ regAt ξ p) ∧ OrderAt L (c₀ • e₀) 1 1 0 p) ∨ ∃ (v : HeightOneSpectrum (𝓞 F)) (π : F) (m : ℕ) (n : ℤ), (∀ a : F, v.valuation F a ≤ 1 → φ a ∈ regAt ξ p) ∧ v.valuation F π = WithZero.exp (-1 : ℤ) ∧ 0 < m ∧ (n : ℚ) = m * r v ∧ OrderAt L (c₀ • e₀) (φ π) m n p) → (∀ σ, 0 < cinf σ) → (∀ (σ : F →+* ℂ) z (g h : MRing ι) (dg dh : K → ℕ), PtOver y φ σ z → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) → ∃ S : FlatHerm y φ A, S.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F : ℝ) := by
  exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_of_adelic
