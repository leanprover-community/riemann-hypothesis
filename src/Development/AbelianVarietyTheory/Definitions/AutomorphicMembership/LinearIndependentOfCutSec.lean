module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TopForm Formalism.BasicNotions
open scoped ComplexOrder

namespace GlobalTheory.TrueGeo

namespace Res

section Val

variable {K K' : Type} [Field K] [Field K'] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f g : Z.functionField}

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dite_eq_left h, IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec]

variable {y}

variable (y)

variable {y} in
theorem valAt_fnOf {U : Z.Opens} (hy : below y ∈ U) (h : genericPoint Z ∈ U) (a : Γ(Z, U)) :
    valAt y (fnOf U h a) = TangentOrigin.evalPt y U ((Points.le_preimage_iff _ _).2 hy) a := by
  rw [← algebraMap_germ hy a, valAt_algebraMap]
  exact congrArg (fun q => q.hom a) (Scheme.germ_stalkClosedPointTo y U hy)

theorem ratVal_eq_valAt {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} (z : CxPts q σ)
    (hf : RegAt (under z) f) : ratVal f z = valAt z.1 f := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  rw [ratVal_fnOf (CxPts.mem_ptsIn.2 hU), valAt_fnOf hU, CxPts.ev_eq (CxPts.mem_ptsIn.2 hU)]
  rfl

end Val

end Res

open Res

variable {F : Type} [Field F] [NumberField F] (Y : Var F)

variable (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ} (w : Fin n → Y.Fn)
  (c : Fin Y.dim → Fin n → 𝓞 E)

instance galAction : MulAction (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (GeomPt Y E) where
  smul σ y := ⟨spMap (σ : AlgebraicClosure E →+* AlgebraicClosure E) ≫ y.1, by
    rw [Category.assoc, y.2, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun a => σ.commutes _)⟩
  one_smul y := Subtype.ext ((congrArg (· ≫ y.1) (Spec.map_id _)).trans (Category.id_comp _))
  mul_smul σ τ y := Subtype.ext (by
    change spMap _ ≫ y.1 = spMap _ ≫ spMap _ ≫ y.1
    rw [← Category.assoc, ← spMap_comp]
    rfl)

section Gal

variable {Y E} (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (y : GeomPt Y E)

end Gal

instance galActionCut : MulAction (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (cutSet Y E w c) where
  smul σ y := ⟨σ • y.1, smul_mem_cutSet σ y.2⟩
  one_smul y := Subtype.ext (one_smul _ y.1)
  mul_smul σ τ y := Subtype.ext (mul_smul σ τ y.1)

section Indep

variable {Y E w c} {x : Y.X} {y : GeomPt Y E} {k k' : Fin n} {g g' e : Y.Fnˣ} {Δ : Y.Dv} {f f' : Y.Fn}

end Indep

section Herm

variable {Y E}

variable {C : CxSt F} (A : Adl C Y)

end Herm

variable [StarRing F] (M0 : HLat F) (ι₀ : M0.V →ₗ[F] Y.Fn)

variable {C : CxSt F} (A : Adl C Y)

section OnePoint

variable {Y E w c} [Unique (cutSet Y E w c)]

end OnePoint

end GlobalTheory.TrueGeo
