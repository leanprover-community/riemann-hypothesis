import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.PsJetEqToJetOfNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm

namespace GlobalTheory.HeightParts

attribute [local instance] Over.cartesianMonoidalCategory

section Lat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  {K : Type} [Field K] [NumberField K] {xO : Sp (𝓞 K) ⟶ X} {xK : Sp K ⟶ X}

def lieCoordLat (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = xK) {n : ℕ} (b : Fin n → TanM xK t.G) :
    Submodule (𝓞 K) (Fin n → K) where
  carrier := {c | ∃ w : TanM xO t.G, bcTan (algebraMap (𝓞 K) K) hx w = ∑ i, c i • b i}
  add_mem' := by
    rintro c c' ⟨w, hw⟩ ⟨w', hw'⟩
    refine ⟨w + w', ?_⟩
    rw [map_add, hw, hw', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (add_smul _ _ _).symm
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro a c ⟨w, hw⟩
    refine ⟨a • w, ?_⟩
    rw [map_smulₛₗ, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, Algebra.smul_def, mul_smul]

end Lat

variable {D : D7} (O : Setup D)

def IsLieAt (y : Pt O.s) (K : Type) [Field K] [NumberField K] (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K))
    (h : HermFam K (Fin (D.R.f * O.N) → K)) : Prop :=
  ∃ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (io : K →+* Qb) (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z)
    (xO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = yK ≫ genι O.s.T.Z)
    (hio : spMap io ≫ yK = y.y) (e : Fin (D.R.f * O.N) ≃ Letter O.S.Dw)
    (b : Fin (D.R.f * O.N) → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G),
    O.CoreWith x P ∧ yK ≫ genStr O.s.T.Z = spMap fK ∧
    (∀ i, (tv (bcTan io (by rw [← Category.assoc, hio]) (b i))).left = y.u (e i).1 (e i).2) ∧
    L = lieCoordLat O.s.T.Z.t hx b ∧
    ∀ (σ : K →+* ℂ) (z : CxPts (genStr O.s.T.Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin (D.R.f * O.N) → K),
      h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i))
        (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i))

end GlobalTheory.HeightParts

end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi Formalism.L2.Pj
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt

namespace GlobalTheory.HeightParts

section Gram

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] (h : HermFam K V) (σ : K →+* ℂ)

theorem hermFam_add_left (x y z : V) : h.form σ (x + y) z = h.form σ x z + h.form σ y z := by
  rw [← h.conj_symm σ z (x + y), h.add_right, map_add, h.conj_symm, h.conj_symm]

theorem hermFam_smul_left (a : K) (x y : V) : h.form σ (a • x) y = starRingEnd ℂ (σ a) * h.form σ x y := by
  rw [← h.conj_symm σ y (a • x), h.smul_right, map_mul, h.conj_symm]

theorem hermFam_sum_sum {α β : Type} [Fintype α] [Fintype β] (c : α → K) (x : α → V) (d : β → K) (y : β → V) :
    h.form σ (∑ i, c i • x i) (∑ j, d j • y j) =
      ∑ i, ∑ j, starRingEnd ℂ (σ (c i)) * σ (d j) * h.form σ (x i) (y j) := by
  classical
  have hl : ∀ (s : Finset α) (z : V), h.form σ (∑ i ∈ s, c i • x i) z = ∑ i ∈ s, h.form σ (c i • x i) z := by
    intro s z
    induction s using Finset.induction_on with
    | empty =>
      have := hermFam_add_left h σ 0 0 z
      simp only [add_zero] at this
      simp only [Finset.sum_empty]
      linear_combination -this
    | insert a s ha ih => rw [Finset.sum_insert ha, hermFam_add_left, ih, Finset.sum_insert ha]
  have hr : ∀ (s : Finset β) (z : V), h.form σ z (∑ j ∈ s, d j • y j) = ∑ j ∈ s, h.form σ z (d j • y j) := by
    intro s z
    induction s using Finset.induction_on with
    | empty =>
      have := h.add_right σ z 0 0
      simp only [add_zero] at this
      simp only [Finset.sum_empty]
      linear_combination -this
    | insert a s ha ih => rw [Finset.sum_insert ha, h.add_right, ih, Finset.sum_insert ha]
  rw [hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hr]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hermFam_smul_left, h.smul_right]
  ring

theorem hermFam_gram_posSemidef {n : ℕ} (v : Fin n → V) : (h.gram σ v).PosSemidef := by
  classical
  let W := Submodule.span K (Set.range v)
  haveI : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range v)
  let b := Module.finBasis K W
  have hb : LinearIndependent K (fun i => (b i : V)) := b.linearIndependent.map' W.subtype W.ker_subtype
  let g : Matrix (Fin n) (Fin (Module.finrank K W)) K :=
    Matrix.of fun i j => b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ j
  have hf : ∀ i, v i = ∑ j, g i j • (b j : V) := fun i => by
    have := congrArg W.subtype (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩).symm
    rw [map_sum] at this
    simpa [g] using this
  have hG := (h.posDef σ _ _ hb).posSemidef
  let B : Matrix (Fin n) (Fin (Module.finrank K W)) ℂ := Matrix.of fun i j => starRingEnd ℂ (σ (g i j))
  let G : Matrix (Fin (Module.finrank K W)) (Fin (Module.finrank K W)) ℂ := Matrix.of fun i j => h.form σ (b i : V) (b j)
  have e : h.gram σ v = B * G * B.conjTranspose := by
    ext i j
    simp only [HermFam.gram, G, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, B, RCLike.star_def,
      Complex.conj_conj]
    rw [hf i, hf j, hermFam_sum_sum, Finset.sum_comm]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [e]
  exact hG.mul_mul_conjTranspose_same B

end Gram

section Mono

variable {K : Type} [Field K] [NumberField K] {m r m' : ℕ} {h : HermFam K (Fin m → K)}
  {L : Submodule (𝓞 K) (Fin m → K)} {ε : Fin r → Fin m → K} {q : (Fin m → K) →ₗ[K] (Fin m' → K)}
  {h' : HermFam K (Fin m' → K)} {L' : Submodule (𝓞 K) (Fin m' → K)}

theorem torusExt_mono {C C' : ℝ} (hT : TorusExt h L ε q h' L' C) (hC : C ≤ C') : TorusExt h L ε q h' L' C' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, hm⟩ := hT
  have hd : (0 : ℂ) ≤ ((C' - C : ℝ) : ℂ) := Complex.zero_le_real.2 (sub_nonneg.2 hC)
  refine ⟨a1, a2, a3, a4, a5, a6, a7, fun σ => ⟨?_, fun n v => ?_⟩⟩
  · have := (hm σ).1.add ((hermFam_gram_posSemidef h σ ε).smul hd)
    convert this using 1
    push_cast
    module
  · have := ((hm σ).2 n v).add ((hermFam_gram_posSemidef h σ v).smul hd)
    convert this using 1
    push_cast
    module

end Mono

section With

variable {D : D7} (O : Setup D)

def IsLieAtWith (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ) (y : Pt O.s) (K : Type) [Field K] [NumberField K] (io : K →+* Qb)
    (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (h : HermFam K (Fin (D.R.f * O.N) → K)) : Prop :=
  ∃ (fK : O.κ.c.F →+* K) (yK : Sp K ⟶ gen O.s.T.Z)
    (xO : Sp (𝓞 K) ⟶ O.s.T.Z.X) (hx : spMap (algebraMap (𝓞 K) K) ≫ xO = yK ≫ genι O.s.T.Z)
    (hio : spMap io ≫ yK = y.y) (e : Fin (D.R.f * O.N) ≃ Letter O.S.Dw)
    (b : Fin (D.R.f * O.N) → TanM (yK ≫ genι O.s.T.Z) O.s.T.Z.t.G),
    O.CoreWith x P ∧ yK ≫ genStr O.s.T.Z = spMap fK ∧
    (∀ i, (tv (bcTan io (by rw [← Category.assoc, hio]) (b i))).left = y.u (e i).1 (e i).2) ∧
    L = lieCoordLat O.s.T.Z.t hx b ∧
    ∀ (σ : K →+* ℂ) (z : CxPts (genStr O.s.T.Z) (σ.comp fK)) (hz : z.1 = spMap σ ≫ yK) (u v : Fin (D.R.f * O.N) → K),
      h.form σ u v = x.met (σ.comp fK) z (bcTan σ (by rw [hz, Category.assoc]) (∑ i, v i • b i))
        (bcTan σ (by rw [hz, Category.assoc]) (∑ i, u i • b i))

variable {O} in

theorem IsLieAtWith.isLieAt {x : ToroidalCompactificationData O.s} {P : PolOf x O.Φ} {y : Pt O.s} {K : Type} [Field K] [NumberField K]
    {io : K →+* Qb} {L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)} {h : HermFam K (Fin (D.R.f * O.N) → K)}
    (hw : IsLieAtWith O x P y K io L h) : IsLieAt O y K L h := by
  obtain ⟨fK, yK, xO, hx, hio, e, b, h₁, h₂, h₃, h₄, h₅⟩ := hw
  exact ⟨x, P, io, fK, yK, xO, hx, hio, e, b, h₁, h₂, h₃, h₄, h₅⟩

end With

end GlobalTheory.HeightParts

end
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam.Pad GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps

namespace GlobalTheory.BdFib

attribute [local instance] Over.cartesianMonoidalCategory

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

def FibAt {k : Type} [Field k] (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G) : Prop :=
  IsGrpPullback φ.G t.G x m.F ∧ m.e = x ∧ m.IsPullCubical φ.cub t.cub

def IsCochFrame {R : Type} [CommRing R] (x : Sp R ⟶ X) {r : ℕ} (ε : Fin r → TanM x t.G) : Prop :=
  ∃ u : torus R r ⟶ (Over.pullback x).obj t.G, IsMonHom u ∧ IsClosedImmersion u.left ∧
    ∀ i, ∃ e : LieG (torus R r), lieCoord e = Pi.single i 1 ∧
      (tv (ε i)).left = e.1.left ≫ u.left ≫ pullback.fst t.G.hom x

def TorRk {k : Type} [Field k] (x : Sp k ⟶ X) (r : ℕ) : Prop :=
  ∀ T : TorusExtension ((Over.pullback x).obj t.G), @Module.finrank ℤ T.X _ T.addCommGroup.toAddCommMonoid _ = r

variable {t}

def IsAbMap {k : Type} [Field k] {x : Sp k ⟶ X} (φ : Fib k) (m : CubeMap φ.G t.G) {n : ℕ} (v : Fin n → (epsR k ⟶ φ.P.A))
    (q : TanM x t.G →ₗ[k] (Fin n → k)) : Prop :=
  ∀ w : TanM x t.G, ∃ w' : epsR k ⟶ φ.G, w'.left ≫ m.F = (tv w).left ∧ IsLieComb (q w) v (w' ≫ φ.q)

def AbLe {z : Sp ℂ ⟶ X} (g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ) (C : ℝ) : Prop :=
  ∀ (φ : Fib ℂ) (m : CubeMap φ.G t.G), FibAt t z φ m → ∀ (n : ℕ), φ.P.g = n → ∀ (u : HolUnif φ.P.A φ.P.L n)
    (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    ∀ (v : TanM z t.G) (v' : epsR ℂ ⟶ φ.G) (W : Fin n → ℂ), v'.left ≫ m.F = (tv v).left → u.IsDiff W (v' ≫ φ.q) →
      Real.pi * (hermForm Hm W W).re ≤ C * (g v v).re

theorem AbLe.mono {z : Sp ℂ ⟶ X} {g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ} (hg : IsBlockMetric g) {C C' : ℝ}
    (h : AbLe g C) (hC : C ≤ C') : AbLe g C' := fun φ m hφ n e u Hm χ hA v v' W h₁ h₂ => by
  refine (h φ m hφ n e u Hm χ hA v v' W h₁ h₂).trans (mul_le_mul_of_nonneg_right hC ?_)
  by_cases hv : v = 0
  · simp [hv]
  · exact (hg.2.1 v hv).le

end Fibre

def HasModel {K : Type} [Field K] [NumberField K] (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (G : Over (Sp (𝓞 K))) (_ : GrpObj G) (θ : A.left ⟶ G.left), IsSemiAbelian G ∧
    IsGrpPullback A G (spMap (algebraMap (𝓞 K) K)) θ

section Large

variable {Y : Scheme.{0}}

def Large (y : Sp Qb ⟶ Y) (Q : ∀ (K : Type) [Field K] [NumberField K], (Sp K ⟶ Y) → Prop) : Prop :=
  ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb),
    ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ →
      ∀ yK : Sp K ⟶ Y, spMap io ≫ yK = y → Q K yK

theorem exists_common {K₁ K₂ : Type} [Field K₁] [NumberField K₁] [Field K₂] [NumberField K₂] (i₁ : K₁ →+* Qb)
    (i₂ : K₂ →+* Qb) : ∃ (K : Type) (_ : Field K) (_ : NumberField K) (i : K →+* Qb) (j₁ : K₁ →+* K) (j₂ : K₂ →+* K),
      i.comp j₁ = i₁ ∧ i.comp j₂ = i₂ := by
  let a₁ : K₁ →ₐ[ℚ] Qb := i₁.toRatAlgHom
  let a₂ : K₂ →ₐ[ℚ] Qb := i₂.toRatAlgHom
  haveI : FiniteDimensional ℚ a₁.fieldRange := a₁.toLinearMap.finiteDimensional_range
  haveI : FiniteDimensional ℚ a₂.fieldRange := a₂.toLinearMap.finiteDimensional_range
  let K : IntermediateField ℚ Qb := a₁.fieldRange ⊔ a₂.fieldRange
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField K := ⟨⟩
  refine ⟨K, inferInstance, inferInstance, algebraMap K Qb,
    i₁.codRestrict K.toSubfield fun a => (le_sup_left : a₁.fieldRange ≤ K) ⟨a, rfl⟩,
    i₂.codRestrict K.toSubfield fun a => (le_sup_right : a₂.fieldRange ≤ K) ⟨a, rfl⟩, rfl, rfl⟩

variable {y : Sp Qb ⟶ Y} {Q Q' : ∀ (K : Type) [Field K] [NumberField K], (Sp K ⟶ Y) → Prop}

theorem Large.and (h : Large y Q) (h' : Large y Q') : Large y fun K _ _ yK => Q K yK ∧ Q' K yK := by
  obtain ⟨K₁, _, _, i₁, h₁⟩ := h
  obtain ⟨K₂, _, _, i₂, h₂⟩ := h'
  obtain ⟨K₀, _, _, i, j₁, j₂, e₁, e₂⟩ := exists_common i₁ i₂
  refine ⟨K₀, _, inferInstance, i, fun K _ _ io j hj yK hy => ⟨h₁ K io (j.comp j₁) ?_ yK hy, h₂ K io (j.comp j₂) ?_ yK hy⟩⟩
  · rw [← RingHom.comp_assoc, hj, e₁]
  · rw [← RingHom.comp_assoc, hj, e₂]

theorem epi_spMap {K L : Type} [Field K] [Field L] (f : K →+* L) : Epi (spMap f) := by
  letI := f.toAlgebra
  have h₁ : Flat (spMap f) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact inferInstanceAs (Module.Flat K L)
  have h₂ : Surjective (spMap f) := ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem Large.of_point {K₀ : Type} [Field K₀] [NumberField K₀] (io₀ : K₀ →+* Qb) (y₀ : Sp K₀ ⟶ Y)
    (hy : spMap io₀ ≫ y₀ = y)
    (h : ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ → Q K (spMap j ≫ y₀)) :
    Large y Q := by
  refine ⟨K₀, _, inferInstance, io₀, fun K _ _ io j hj yK hK => ?_⟩
  have := epi_spMap io
  have e : yK = spMap j ≫ y₀ := by
    rw [← cancel_epi (spMap io), hK, ← hy, ← hj, ← Category.assoc, ← Spec.map_comp]
    rfl
  exact e ▸ h K io j hj

end Large

end GlobalTheory.BdFib

end
end
