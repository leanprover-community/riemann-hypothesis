module

public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MeanSquareMultipleThetaSectionFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.meanSquare_multiple_thetaSection_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))) (fr : Xo.univ.t.PP.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (F.Di k).La) (b : Fin m → ℂ) (h τ : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ) (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (κ : ℂ), b ∈ B → IsPeriod (F.Di k) ty (P b) → (∀ v w, (F.Di k).EF (bas v) (bas w) = -omegaStd v w) → IsUnit h.det → τ.IsSymm → (τ.map Complex.im).PosDef → (∀ i, h *ᵥ P b (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧ h *ᵥ P b (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) → (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) → RigFrame F k B P fr → x = F.u k (P b) → κ ≠ 0 → SecVal F k (P b) x s (fun z => κ * thetaChar τ c₁ c₂ (h *ᵥ z)) (fun j z => fr j (b, z)) → AHMean F k (P b) x s (‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹) := by
  first | exact @GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar | exact GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar | (intros; apply GlobalTheory.FrameNorm.ahMean_of_secVal_thetaChar <;> assumption)
