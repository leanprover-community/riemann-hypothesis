module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaElementLevelFourSquare
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.exists_symmetric_thetaElement_level_four_square : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ A.A), x ^ 4 = 1 → ∀ σ : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(ι[A.A]).left, 𝟙 A.A.left] ![1, -1]), σ.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ σ (eSec A.A)) (LB.oneGen A.L) → ∃ θ : ThetaGrp A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F), θ.pt = x ∧ (∃ nu : LB.Gen (negLB A.A A.L ((4 : ℕ) : ℤ) (TFK (R := R) F)), nu.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (symGen A.A A.L ((4 : ℕ) : ℤ) θ nu) (LB.oneGen A.L)) ∧ ∃ c : F, (∀ z J, Good A.L z J → (val σ (x ^ 2).left z J).val = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c)) ∧ ∀ (ψ : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) F ⊗ A.A) (m : TFK (R := R) F ⊗ A.A ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ^ 2 → ∀ α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![((4 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]), α.IsGen → ∀ (t : SecA A F 1) (t₁ t₂ t₃ : SecA A F 4), IsTwistPull A.A A.L ψ m hm ((4 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α t t₁ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₁ t₂ → IsActOf A.A A.L ((4 : ℕ) : ℤ) θ t₂ t₃ → ∀ j, t₃.f j = liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) * t₁.f j := by
  first | exact @GlobalTheory.ThetaSquare.exists_symmetric_square | exact GlobalTheory.ThetaSquare.exists_symmetric_square | (intros; apply GlobalTheory.ThetaSquare.exists_symmetric_square <;> assumption)
