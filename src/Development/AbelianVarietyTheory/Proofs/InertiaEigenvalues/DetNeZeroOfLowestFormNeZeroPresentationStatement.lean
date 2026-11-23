module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetNeZeroOfLowestFormNeZeroPresentation
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.det_ne_zero_of_lowestForm_ne_zero_presentation : ∀ (A B : Type) [CommRing A] [CommRing B] (π : B →+* A) (x y : B) (μ : Type) [Fintype μ] (a a' : ℕ) (Φ' : Matrix (Fin a') (Fin a') B) (u t : μ → Fin a' → B) (η : μ → B) (Φ : Matrix (Fin a) (Fin a) A) (E : Matrix (Fin a) (Fin a') A) (U : μ → Fin a → A) (k : μ → A) (l₀ : Fin a), Function.Surjective π → (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) → π x = 0 → π y = 0 → x * x = 0 → y ^ Fintype.card μ = 0 → (∀ f, x * y ^ (Fintype.card μ - 1) * f = 0 → π f = 0) → (∀ j, π (η j) = 1) → (∀ j, x • u j - (y * η j) • t j ∈ what₂ Φ') → what₂ E ⊔ (what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) = ⊤ → (∀ b, (Φ * E) b ∈ what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) → (∀ j, (fun c => π (u j c)) - Matrix.vecMul (U j) E ∈ what₂ (Φ'.map π) ⊔ what₂ (fun j c => π (t j c))) → ∑ j, k j • (fun c => π (t j c)) ∈ what₂ (Φ'.map π) → ∑ j, k j * ∑ c, U j c * Φ.adjugate c l₀ ≠ 0 → Φ'.det ≠ 0 := by
  first | exact @GlobalTheory.LowDet.det_ne_zero | exact GlobalTheory.LowDet.det_ne_zero | (intros; apply GlobalTheory.LowDet.det_ne_zero <;> assumption)
