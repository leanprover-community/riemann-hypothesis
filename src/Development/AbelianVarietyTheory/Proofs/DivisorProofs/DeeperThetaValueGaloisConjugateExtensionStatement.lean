module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperThetaValueGaloisConjugateExtension
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.deeperTheta_value_galoisConjugate_extension : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {z₂ : 𝔗.X₂.M.Z} {V' : Type} [CommRing V'] [IsDomain V'] (ev₂ ev₂' : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → RegAt 𝔗.X₂ z₂ ev₂ → RegAt 𝔗.X₂ z₂ ev₂' → ∀ a : 𝔗.X₂.S.R, 𝔗.X₂.M.val (jK V' ≫ spMap ev₂' ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) a = 𝔗.X₂.M.val (jK V' ≫ spMap ev₂ ≫ 𝔗.X₂.M.Z.fromSpecStalk z₂) (𝔗.sR σ a) := by
  first | exact @GlobalTheory.Poinc.Sep.val_galois_conj | exact GlobalTheory.Poinc.Sep.val_galois_conj | (intros; apply GlobalTheory.Poinc.Sep.val_galois_conj <;> assumption)
