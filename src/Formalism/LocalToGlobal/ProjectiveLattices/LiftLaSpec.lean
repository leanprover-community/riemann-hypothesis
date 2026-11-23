module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Dw) in
abbrev LaMod (l : Level H) : Type := Dw.La ⧸ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La))

variable (Dw) in
def G0 (l₁ l : Level H) : Subgroup (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) where
  carrier := {γ | ∀ q : LaMod Dw l, γ q - q ∈
    (l₁.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).map (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ}
  one_mem' := fun q => by simp
  mul_mem' := by
    intro γ δ hγ hδ q
    have h := Submodule.add_mem _ (hγ (δ q)) (hδ q)
    rwa [sub_add_sub_cancel] at h
  inv_mem' := by
    intro γ hγ q
    have h := Submodule.neg_mem _ (hγ (γ⁻¹ q))
    have e : γ (γ⁻¹ q) = q := γ.apply_symm_apply q
    rwa [e, neg_sub] at h

def liftLa (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) : Dw.La →ₗ[𝓞 E] Dw.La :=
  haveI := Dw.proj
  (Module.projective_lifting_property (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ
    (γ.toLinearMap ∘ₗ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ)
    (Submodule.mkQ_surjective _)).choose

theorem liftLa_spec (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) (a : Dw.La) :
    (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ (liftLa γ a) = γ ((l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ a) := by
  have := Dw.proj
  exact LinearMap.congr_fun (Module.projective_lifting_property (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ
    (γ.toLinearMap ∘ₗ (l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)).mkQ) (Submodule.mkQ_surjective _)).choose_spec a

def levG {l₁ : Level H} (γ : G0 Dw l₁ l) : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La) :=
  (liftLa (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l), LinearMap.id)

variable (Xo : Moduli Dw l) (c : Coeff l)

def hkScal (cq : c.F) (𝔓 : Ideal (𝓞 E)) (i n : ℕ) : c.F :=
  cq * ((Ideal.absNorm 𝔓 : c.F)⁻¹) ^ (i * n / 2)

end Formalism.L2.Pj
