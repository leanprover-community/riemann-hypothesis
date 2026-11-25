module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

variable (l : ℕ) [Fact l.Prime]

abbrev Htot (E : Spc) : Type 1 := DirectSum ℤ fun n : ℤ => HQ l E n 0

def pullTot {E E' : Spc} (f : E ⟶ E') : Htot l E' →ₗ[ℚ_[l]] Htot l E :=
  DirectSum.lmap fun n => pullHQ l f n 0

theorem pullTot_id (E : Spc) : pullTot l (𝟙 E) = LinearMap.id := by
  simp only [pullTot, pullHQ, pullHl_id, LinearMap.baseChange_id]
  exact DirectSum.lmap_id

theorem pullTot_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') :
    pullTot l (f ≫ g) = pullTot l f ∘ₗ pullTot l g := by
  simp only [pullTot, pullHQ, pullHl_comp, LinearMap.baseChange_comp]
  exact DirectSum.lmap_comp _ _

def galTot {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    (Ω ≃ₐ[k] Ω) → Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) →ₗ[ℚ_[l]] Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) :=
  fun σ => pullTot l (sch.map (GlobalTheory.Et.galMap Ω p σ))

theorem galTot_one {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    galTot l Ω p 1 = LinearMap.id := by
  simp only [galTot]
  rw [_root_.GlobalTheory.EtC.galMap_one, CategoryTheory.Functor.map_id, pullTot_id]

theorem galTot_mul {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))
    (σ τ : Ω ≃ₐ[k] Ω) : galTot l Ω p (σ * τ) = galTot l Ω p σ ∘ₗ galTot l Ω p τ := by
  simp only [galTot]
  rw [_root_.GlobalTheory.EtC.galMap_mul, CategoryTheory.Functor.map_comp, pullTot_comp]

def galTotRep {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    Representation ℚ_[l] (Ω ≃ₐ[k] Ω) (Htot l (sch.obj (GlobalTheory.Et.geom Ω p))) where
  toFun := galTot l Ω p
  map_one' := galTot_one l Ω p
  map_mul' := galTot_mul l Ω p

def Splits {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) {J : Type} (σ : J → (W ⟶ Y)) : Prop :=
  ∃ h : ∀ j, σ j ≫ s = c,
    IsIso (Limits.Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h j, Category.id_comp])) :
      ∐ (fun _ : J => W) ⟶ pullback s c)

def IsGalois {W X : Scheme.{0}} (c : W ⟶ X) (G : Type) [Group G] (a : G → (W ⟶ W)) : Prop :=
  IsFinite c ∧ Etale c ∧ Surjective c ∧ a 1 = 𝟙 W ∧ (∀ g h, a (g * h) = a g ≫ a h) ∧ Splits c c a

def IsCorrOp {Z Y Z' : Scheme.{0}} (s : Y ⟶ Z) (t : Y ⟶ Z') (T : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) : Prop :=
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (J : Type) (_ : Fintype J)
    (σ : J → (W ⟶ Y)), IsGalois c G a ∧ Splits s c σ ∧
    ∀ x, pullTot l (sch.map c) (T x) = ∑ j, pullTot l (sch.map (σ j ≫ t)) x

variable {l}

def genEig {H : Type*} [AddCommGroup H] [Module ℚ_[l] H] (L : Type*) [Field L] [Algebra ℚ_[l] L] {J : Type*}
    (T : J → H →ₗ[ℚ_[l]] H) (θ : J → L) : Submodule L (TensorProduct ℚ_[l] L (H)) :=
  ⨅ j, Module.End.maxGenEigenspace ((T j).baseChange L) (θ j)

variable (l)

end GlobalTheory.GalV

end
