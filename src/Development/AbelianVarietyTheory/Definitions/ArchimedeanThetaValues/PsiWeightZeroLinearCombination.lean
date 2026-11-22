module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.ToricData

section Const

variable {Z Y W : Scheme.{0}} {J J' : Type} [Fintype J] [Fintype J']

instance isIso_zero2 (S : Scheme.{0}) : IsIso (zero2 (zeroPolAV S).A) := by
  have : (lift η[(zeroPolAV S).A] η[(zeroPolAV S).A] : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ 𝟙_ (Over S)) =
      (λ_ (𝟙_ (Over S))).inv :=
    CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (toUnit_unique _ _)
  change IsIso ((Over.forget S).map
    (lift η[(zeroPolAV S).A] η[(zeroPolAV S).A] : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ 𝟙_ (Over S)))
  rw [this]
  infer_instance

end Const

section UnitOn

variable {A B : Type} [CommRing A] [CommRing B]

theorem unitOn_mul (u v : Aˣ) : unitOn (u * v) = unitOn u * unitOn v := by
  unfold unitOn
  exact map_mul _ _ _

theorem unitOn_bijective : Function.Bijective (unitOn : Aˣ → Γ(Sp A, ⊤)ˣ) := by
  have e : (unitOn : Aˣ → Γ(Sp A, ⊤)ˣ) =
      Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.toMulEquiv := by
    funext u
    ext
    rfl
  rw [e]
  exact (Units.mapEquiv _).bijective

theorem unitOn_inj {u v : Aˣ} : unitOn u = unitOn v ↔ u = v := unitOn_bijective.injective.eq_iff

theorem pullTop_unitOn (f : A →+* B) (u : Aˣ) :
    pullTop (Spec.map (CommRingCat.ofHom f)) (unitOn u) = unitOn (Units.map f.toMonoidHom u) := by
  ext1
  have := congrArg (fun g => g.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

end UnitOn

variable (K : Type) [CommRing K] [IsDomain K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]

variable {K X}

instance (q : X → (FractionRing K)ˣ) (O : Type) [Ring O] [Module O X] : Module O (toricPre K X q).X :=
  inferInstanceAs (Module O X)

variable (q : X → (FractionRing K)ˣ)

variable (F : Type) [Field F] [Algebra (FractionRing K) F]

section Examples

end Examples

end GlobalTheory.ToricData
