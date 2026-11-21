import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcVarZpowInjective

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HostModel

open ToricData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def LevelAgree {D : Datum H} {l : Level H} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k}
    (a : ArcIn D l (RingHom.id c.F) k bF) (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}))
    [Module (𝓞 E) P.toPre.X] {φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
    (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
    (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F]
    (uF : F),
    (∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x))) →
    uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X) →
    ∀ (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n),
      ((n = l.A ∧ ∃ v, HEq p₀ (a.etaA v)) ∨
        (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), HEq p₀ (a.eta v))) →
      ∀ (q₀ : QkPt a.D₀ F n) (q₁ q₂ : QkPt P.toPre F n),
        QkExt (algebraMap _ F) p₀ q₀ → q₁.y = e₁ q₀.y → q₂.y = e₂ q₀.y →
        (∀ z, GenRel w₁ (q₁.g.s (e₁ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
        (∀ z, GenRel w₂ (q₂.g.s (e₂ z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / n))) →
        QkPt.Equiv P.toPre F q₁ q₂


variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)

def witP : DegData (PowerSeries k) (Ideal.span {PowerSeries.X}) :=
  arcData (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF)

instance instModuleWitP : Module (𝓞 E) (witP c k bF).toPre.X := inferInstanceAs (Module (𝓞 E) (𝓞 E))

def witAct : letI := H.starRing; (witP c k bF).toPre.OAct (𝓞 E) :=
  letI := H.starRing
  arcOAct (X := 𝓞 E) k (arcForm l) (arcIn c k bF).be_symm (arcIn c k bF).be_pos (arcIn_be_even c k bF) (𝓞 E)
    (arcIn c k bF).be_adj

def witMap : (witP c k bF).toPre.P.A.left ⟶ (arcIn c k bF).D₀.P.A.left :=
  baseMap (fun _ : 𝓞 E => 1) (PowerSeries.C (R := k)) (arcExp (X := 𝓞 E) k (arcForm l))


def witIso : LB.Iso (witP c k bF).toPre.P.L ((arcIn c k bF).D₀.P.L.pull (witMap c k bF)) :=
  baseIso (fun _ : 𝓞 E => 1) (PowerSeries.C (R := k)) (arcExp (X := 𝓞 E) k (arcForm l))




omit [IsCMField E] in

theorem refl_ne_neg : LinearEquiv.refl (𝓞 E) (𝓞 E) ≠ (LinearEquiv.neg (𝓞 E) : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) := fun h => by
  have h1 : (1 : 𝓞 E) = -1 := congrArg (fun e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E => e 1) h
  exact one_ne_zero (self_eq_neg.1 h1)


section LevelPts

variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]


variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
    algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
include hF

theorem eq_of_genRel {n : ℕ} (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) (x : 𝓞 E → F) (q₀ : QkPt (arcIn c k bF).D₀ F n)
    (q₁ q₂ : QkPt (witP c k bF).toPre F n) (hy : q₁.y = q₂.y)
    (h₁ : ∀ z, GenRel (witIso c k bF) (q₁.g.s (e z)) (q₀.g.s z) (x z))
    (h₂ : ∀ z, GenRel (witIso c k bF) (q₂.g.s (e z)) (q₀.g.s z) (x z)) : q₁ = q₂ := by
  obtain ⟨y₀, g₀, e₀⟩ := q₀
  obtain ⟨y₁, g₁, e₁⟩ := q₁
  obtain ⟨y₂, g₂, e₂⟩ := q₂
  obtain ⟨t₀, rfl⟩ := (pt_bijective (fun _ : 𝓞 E => (1 : (FractionRing k)ˣ)) F).2 g₀
  obtain ⟨t₁, rfl⟩ := (pt_bijective (arcExp (X := 𝓞 E) k (arcForm l)) F).2 g₁
  obtain ⟨t₂, rfl⟩ := (pt_bijective (arcExp (X := 𝓞 E) k (arcForm l)) F).2 g₂
  obtain rfl : y₁ = y₂ := hy
  obtain rfl : t₁ = t₂ := hom_eq_iff.1 fun χ => by
    obtain ⟨z, rfl⟩ := e.surjective χ
    exact Units.ext (((genRel_pt_iff _ _ _ F hF _ _ _ _ _).1 (h₁ z)).trans
      ((genRel_pt_iff _ _ _ F hF _ _ _ _ _).1 (h₂ z)).symm)
  rfl

end LevelPts




theorem exists_common_field : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F)
    (_ : Algebra (FractionRing (PowerSeries k)) F) (_ : Algebra (FractionRing k) F),
    ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)) := by
  let F := AlgebraicClosure (FractionRing (PowerSeries k))
  let g : k →+* F := ((algebraMap (FractionRing (PowerSeries k)) F).comp
    (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)))).comp PowerSeries.C
  refine ⟨F, inferInstance, inferInstance, inferInstance,
    (IsFractionRing.lift (K := FractionRing k) g.injective).toAlgebra, fun x => ?_⟩
  exact IsFractionRing.lift_algebraMap (K := FractionRing k) g.injective x

end GlobalTheory.HostModel
