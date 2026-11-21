import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.IsPtOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.RootOfCharpoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.TanCocIsBK
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BlochKatoNonpositiveWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.LiftingTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KatoEulerSystems.KatoNOfKato
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ClsEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsUnitPowNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.PtShape
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.Lit.KN.ReducibleThreeDim

open TensorProduct in
private theorem bk_map {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {C : Type} [CommRing C] [Algebra ℚ_[l] C]
    {V : Type} [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousConstSMul C V]
    {V' : Type} [AddCommGroup V'] [Module C V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] C V'] [TopologicalSpace V']
    [IsTopologicalAddGroup V'] [ContinuousConstSMul C V']
    (ρ : Representation C (G F Ω) V) (ρ' : Representation C (G F Ω) V') (f : V →ₗ[C] V') (hfc : Continuous f)
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) {γ : G F Ω → V} (h1 : γ ∈ Z1 ρ) (h2 : Af.IsBK l ρ γ) :
    (fun g => f (γ g)) ∈ Z1 ρ' ∧ Af.IsBK l ρ' (fun g => f (γ g)) := by
  refine ⟨⟨hfc.comp h1.1, fun g h => by simp only [h1.2 g h, map_add, hf]⟩, fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := h2.away w hw
    exact ⟨A, hA, f x, fun s hs => by simp only [hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨hc, hcc⟩, x, hx⟩ := h2.above τ
    refine ⟨j, hj, ⟨hfc.comp hc, fun g h => ?_⟩, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
    · have := congrArg f (hcc g h)
      rw [map_add] at this
      exact this.trans (congrArg _ (hf _ _))
    · have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
          (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype)
            (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
          Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype)
            (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
            (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a b => simp [Loc.actC, hf]
        | add a b ha hb => simp only [map_add, ha, hb]
      rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
      rfl

section Alg

variable {R : Type} [CommRing R]

private def IsBlockSL2Embedding (x : GG 3 R) : Prop :=
  ∃ a b c d : R, a * d - b * c = 1 ∧ x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]

private theorem theta_eq (X : Matrix (Fin 3) (Fin 3) R) :
    thetaLie X = !![-X 2 2, -X 1 2, -X 0 2; -X 2 1, -X 1 1, -X 0 1; -X 2 0, -X 1 0, -X 0 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [thetaLie, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

private theorem conj_eq (a b c d : R) (Y : Matrix (Fin 3) (Fin 3) R) :
    !![a, 0, b; 0, 1, 0; c, 0, d] * Y * !![d, 0, -b; 0, 1, 0; -c, 0, a] =
    !![(a * Y 0 0 + b * Y 2 0) * d - (a * Y 0 2 + b * Y 2 2) * c, a * Y 0 1 + b * Y 2 1,
        -(a * Y 0 0 + b * Y 2 0) * b + (a * Y 0 2 + b * Y 2 2) * a;
      Y 1 0 * d - Y 1 2 * c, Y 1 1, -Y 1 0 * b + Y 1 2 * a;
      (c * Y 0 0 + d * Y 2 0) * d - (c * Y 0 2 + d * Y 2 2) * c, c * Y 0 1 + d * Y 2 1,
        -(c * Y 0 0 + d * Y 2 0) * b + (c * Y 0 2 + d * Y 2 2) * a] := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem ad_eq {x : GG 3 R} {a b c d : R} (h : a * d - b * c = 1)
    (hx : x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]) (X : Matrix (Fin 3) (Fin 3) R) :
    x.adFun X = !![a, 0, b; 0, 1, 0; c, 0, d] * (if x.right = 1 then X else thetaLie X) *
      !![d, 0, -b; 0, 1, 0; -c, 0, a] := by
  have : ((x.left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = !![d, 0, -b; 0, 1, 0; -c, 0, a] := by
    apply Units.inv_eq_of_mul_eq_one_right
    change x.mat * _ = 1
    rw [hx]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      first | ring1 | linear_combination h
  rw [GG.adFun, this, hx]

private def pA : Matrix (Fin 3) (Fin 3) R →ₗ[R] Matrix (Fin 2) (Fin 2) R where
  toFun X := !![X 0 0, X 0 2; X 2 0, X 2 2]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp

private def sA : Matrix (Fin 2) (Fin 2) R →ₗ[R] Matrix (Fin 3) (Fin 3) R where
  toFun Y := !![Y 0 0, 0, Y 0 1; 0, 0, 0; Y 1 0, 0, Y 1 1]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp

private def pB (t : R) : Matrix (Fin 3) (Fin 3) R →ₗ[R] (Fin 2 → R) where
  toFun X := ![X 0 1 + t * X 1 2, X 2 1 - t * X 1 0]
  map_add' X Y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a X := by ext i; fin_cases i <;> simp <;> ring

private def sB (t : R) : (Fin 2 → R) →ₗ[R] Matrix (Fin 3) (Fin 3) R where
  toFun v := !![0, v 0, 0; -(t * v 1), 0, t * v 0; 0, v 1, 0]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

private def pC : Matrix (Fin 3) (Fin 3) R →ₗ[R] Matrix (Fin 3) (Fin 3) R where
  toFun X := !![0, 0, 0; 0, X 1 1, 0; 0, 0, 0]
  map_add' X Y := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' a X := by ext i j; fin_cases i <;> fin_cases j <;> simp

private theorem decomp (u : R) (hu : 2 * u = 1) (X : Matrix (Fin 3) (Fin 3) R) :
    X = sA (pA X) + u • sB 1 (pB 1 X) + u • sB (-1) (pB (-1) X) + pC (pC X) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA, pA, sB, pB, pC]
  · linear_combination (-X 0 1) * hu
  · linear_combination (-X 1 0) * hu
  · linear_combination (-X 1 2) * hu
  · linear_combination (-X 2 1) * hu

private theorem pA_sA (Y : Matrix (Fin 2) (Fin 2) R) : pA (sA Y) = Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sA, pA]

private theorem ad_sA {x : GG 3 R} (hx : IsBlockSL2Embedding x) (Y : Matrix (Fin 2) (Fin 2) R) :
    sA (pA (x.adFun (sA Y))) = x.adFun (sA Y) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [sA, pA]

private theorem pA_ad {x : GG 3 R} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    pA (x.adFun X) = pA (x.adFun (sA (pA X))) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, ad_eq h hx, theta_eq, theta_eq, conj_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [sA, pA]

private def wOf (x : GG 3 R) : Matrix (Fin 2) (Fin 2) R :=
  if x.right = 1 then corner x.mat else corner x.mat * Matrix.diagonal ![-1, 1]

private theorem wOf_eq {x : GG 3 R} {a b c d : R} (hx : x.mat = !![a, 0, b; 0, 1, 0; c, 0, d]) :
    wOf x = if x.right = 1 then !![a, b; c, d] else !![-a, b; -c, d] := by
  have : corner x.mat = !![a, b; c, d] := by
    rw [hx]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [wOf, this]
  split_ifs
  · rfl
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

private theorem pB_ad {x : GG 3 R} (hx : IsBlockSL2Embedding x) (t : R) (ht : t * t = 1) (X : Matrix (Fin 3) (Fin 3) R) :
    pB t (x.adFun X) = ((if x.right = 1 then 1 else t) • wOf x) *ᵥ pB t X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq, wOf_eq hx]
  ext i
  split_ifs <;> fin_cases i <;>
    simp [pB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (a * X 1 2 + b * X 1 0) * ht | linear_combination (c * X 1 2 + d * X 1 0) * ht

private theorem ad_sB {x : GG 3 R} (hx : IsBlockSL2Embedding x) (t : R) (ht : t * t = 1) (v : Fin 2 → R) :
    sB t (((if x.right = 1 then 1 else t) • wOf x) *ᵥ v) = x.adFun (sB t v) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq, wOf_eq hx]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;>
    simp [sB, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (c * v 0 - d * v 1) * ht | linear_combination (-a * v 0 + b * v 1) * ht

private theorem pC_ad {x : GG 3 R} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    pC (x.adFun X) = (if x.right = 1 then 1 else -1 : R) • pC X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [pC]

private theorem ad_pC {x : GG 3 R} (hx : IsBlockSL2Embedding x) (X : Matrix (Fin 3) (Fin 3) R) :
    x.adFun (pC X) = (if x.right = 1 then 1 else -1 : R) • pC X := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [ad_eq h hx, theta_eq, conj_eq]
  ext i j
  split_ifs <;> fin_cases i <;> fin_cases j <;> simp [pC]

private theorem pA_ad_one {x : GG 3 R} (hx : IsBlockSL2Embedding x) (h1 : x.right = 1) (w : GL (Fin 2) R)
    (hw : (w : Matrix (Fin 2) (Fin 2) R) = wOf x) (Y : Matrix (Fin 2) (Fin 2) R) :
    pA (x.adFun (sA Y)) = (w : Matrix (Fin 2) (Fin 2) R) * Y * (w⁻¹ : GL (Fin 2) R) := by
  obtain ⟨a, b, c, d, h, hx⟩ := hx
  rw [wOf_eq hx, if_pos h1] at hw
  have : ((w⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![d, -b; -c, a] := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination h
  rw [ad_eq h hx, if_pos h1, this, hw, conj_eq]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [sA, pA] <;> ring

private theorem pA_ad_c {x : GG 3 R} (hx : x.mat = 1) (h1 : x.right = -1) (Y : Matrix (Fin 2) (Fin 2) R) :
    pA (x.adFun (sA Y)) = -(Jmat R 2 * Yᵀ * Jmat R 2) := by
  have hx' : x.mat = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
    rw [hx]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [ad_eq (by ring) hx', if_neg (by rw [h1]; decide), theta_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sA, pA, Jmat, Fin.rev, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

private def repA {Γ : Type} [Group Γ] (r : Γ →* GG 3 R) (hr : ∀ g, IsBlockSL2Embedding (r g)) :
    Representation R Γ (Matrix (Fin 2) (Fin 2) R) where
  toFun g := pA ∘ₗ adRep r g ∘ₗ sA
  map_one' := by
    refine LinearMap.ext fun Y => ?_
    simp [pA_sA]
  map_mul' g h := by
    refine LinearMap.ext fun Y => ?_
    change pA ((r (g * h)).adFun (sA Y)) = pA ((r g).adFun (sA (pA ((r h).adFun (sA Y)))))
    rw [ad_sA (hr h), map_mul, GG.adFun_mul]

private theorem symp_eq (w : Matrix (Fin 2) (Fin 2) R) :
    wᵀ * !![0, 1; -1, 0] * w = w.det • !![0, 1; -1, 0] := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem pair_eq (w : Matrix (Fin 2) (Fin 2) R) :
    wᵀ * Jmat R 2 * (!![-1, 0; 0, 1] * w * !![-1, 0; 0, 1]) = w.det • Jmat R 2 := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Jmat, Fin.rev] <;> ring

private theorem isBlock_reducible_three_dim {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Rˣ) (g : Γ) : IsBlockSL2Embedding (r0 η Ψ g) := by
  refine ⟨(Ψ g : R), 0, 0, ((Ψ g)⁻¹ : Rˣ), by simp, ?_⟩
  rw [GG.mat, unitaryThreeReflection_left, tor_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wt1]

private theorem pC_mem (X : Matrix (Fin 3) (Fin 3) R) : pC X ∈ gw R 0 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd (by decide) hab

variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
private theorem cont_pA : Continuous (pA : Matrix (Fin 3) (Fin 3) R → _) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> exact continuous_id.matrix_elem _ _

private theorem cont_pB (t : R) : Continuous (pB t) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_id.matrix_elem 0 1).add (continuous_const.mul (continuous_id.matrix_elem 1 2))
  · exact (continuous_id.matrix_elem 2 1).sub (continuous_const.mul (continuous_id.matrix_elem 1 0))

omit [IsTopologicalRing R] in
private theorem cont_pC : Continuous (pC : Matrix (Fin 3) (Fin 3) R → _) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> first | exact continuous_const | exact continuous_id.matrix_elem 1 1

end Alg

end UpperTheory.V.Lit.KN.ReducibleThreeDim

open UpperTheory.V.Lit.KN.ReducibleThreeDim in
theorem UpperTheory.V.Lit.KN.blochKatoSelmer_adRep_vanishes_of_typeII_modular :
    Lit.InpN → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ {r : G ℚ Ω →* GG 3 (PadicAlgCl l)} (h : D.IsPt U g₁ r), ∀ (ι : Qbar l ≃+* ℂ),
      TypeII D.η r → (∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → D.IsModular ι W) → Af.BlochKatoSelmerVanishes l (adRep r) := by
  intro inp Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hm r h ι hII hmod
  obtain ⟨hcc, hηc, -, hlc, -, -, -, hCM, -⟩ := dat_facts D
  obtain ⟨h11, hdet, W, hext, hWc, -, hW, hWd⟩ := typeII_facts inp.toCohInp D hm h hII
  have hirr := typeII_irr_cyc inp.toCohInp D hm h hII W hext
  obtain ⟨f, hf⟩ := hmod W hext
  have hW' : ∀ g, (W g : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) = wOf (r g) := hW
  have hblk0 : ∀ g ∈ D.η.ker, IsBlockSL2Embedding (r g) := by
    intro g hg
    refine ⟨(r g).mat 0 0, (r g).mat 0 2, (r g).mat 2 0, (r g).mat 2 2, ?_, ?_⟩
    · have := hdet g hg
      rw [Matrix.det_fin_two] at this
      exact this
    · ext i j
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | exact h11 g hg
        | exact hII.1 g hg _ _ (by decide)
  have hblk : ∀ g, IsBlockSL2Embedding (r g) := by
    intro g
    rcases Int.units_eq_one_or (D.η g) with hg | hg
    · exact hblk0 g hg
    · have hk : D.η (g * D.cc⁻¹) = 1 := by rw [map_mul, map_inv, hg, hηc, mul_inv_cancel]
      have e1 : r g = r (g * D.cc⁻¹) * r D.cc := by rw [← map_mul, inv_mul_cancel_right]
      have hr : (r (g * D.cc⁻¹)).right = 1 := (h.mult _).trans hk
      have e2 : (r g).mat = (r (g * D.cc⁻¹)).mat := by
        have hrc := h.norm.atc
        rw [e1]
        simp only [GG.mat] at hrc ⊢
        rw [SemidirectProduct.mul_left, hr, sgnAct_one, Units.val_mul, hrc, Matrix.mul_one]
      obtain ⟨a, b, c, d, h1, h2⟩ := hblk0 _ hk
      exact ⟨a, b, c, d, h1, e2.trans h2⟩
  let θ : G ℚ Ω →* (PadicAlgCl l)ˣ := (Units.map (Int.castRingHom (PadicAlgCl l)).toMonoidHom).comp D.η
  have hθ0 : ∀ g, (θ g : PadicAlgCl l) = ((D.η g : ℤˣ) : ℤ) := fun g => rfl
  have hθ : ∀ g, (θ g : PadicAlgCl l) = if (r g).right = 1 then 1 else -1 := by
    intro g
    rw [hθ0, h.mult g]
    rcases Int.units_eq_one_or (D.η g) with hg | hg <;> simp [hg]
  obtain ⟨M, hM, hMk⟩ := CF.kwAbs Ω D.η.ker (hlc.isOpen_fiber 1) (Abelianization.commutator_subset_ker D.η)
  have hθM : Af.KillsMu M θ := by
    intro s hs
    have : D.η s = 1 := hMk s hs
    simp only [θ, MonoidHom.comp_apply, this, map_one]
  have hord : Lit.OrdPoly (e : ℤ) (-(e : ℤ)) W := by
    obtain ⟨A, hA, -⟩ := dat_loc D
    exact ⟨A, N, hA, NeZero.pos N, (typeII_ord inp.toCohInp D hm h hII W hext hWc hWd).2 A hA⟩
  have hB1 := inp.kato l D.gd.l_odd Ω ι e D.gd.e_pos f W hWc hf hord 1 1 le_rfl (fun _ _ => rfl)
  have hB2 := inp.kato l D.gd.l_odd Ω ι e D.gd.e_pos f W hWc hf hord M θ hM hθM
  haveI : IsAlgClosure K Ω := by
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
    exact ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have hker : ∀ s : G K Ω, D.η (s.restrictScalars ℚ) = 1 := fun s => by
    have : galEmb ℚ K Ω s ∈ D.η.ker := D.η_ker ▸ galEmb_mem ℚ K Ω s
    exact this
  have hrc : (r D.cc).right = -1 := (h.mult _).trans hηc
  have hWcc : (W D.cc : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) = !![-1, 0; 0, 1] := by
    have hx' : (r D.cc).mat = !![1, 0, 0; 0, 1, 0; 0, 0, 1] := by
      rw [h.norm.atc]; ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [hW', wOf_eq hx', if_neg (by rw [hrc]; decide), neg_zero]
  have hA : Af.BlochKatoSelmerVanishes l (repA r hblk) := by
    have he := D.gd.e_pos
    refine inp.adQ K D.gd.quad 2 le_rfl l Ω ι W 0 θ hWc (inp.newAut _ (by omega) f l Ω ι W _ hf)
      ⟨M, θ, hM, hθM, by simp⟩ ?_ hirr _ ⟨D.cc, Jgl _ 2, D.conj, fun s s' hs => ?_, fun s X => ?_, fun X => ?_⟩
    · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => ?_⟩
      rw [hθ0, ← hWd s]
      exact symp_eq _
    · have e1 : W (s'.restrictScalars ℚ) = W D.cc * W (s.restrictScalars ℚ) * W D.cc := by
        rw [hs, inv_eq_of_mul_eq_one_right hcc, map_mul, map_mul]
      have e2 := hWd (s.restrictScalars ℚ)
      change (W (s.restrictScalars ℚ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl l))ᵀ * Jmat _ 2 *
        (W (s'.restrictScalars ℚ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl l)) =
          (θ (s.restrictScalars ℚ) : PadicAlgCl l) • Jmat _ 2
      rw [e1, hθ0, ← e2, Units.val_mul, Units.val_mul, hWcc]
      exact pair_eq _
    · exact pA_ad_one (hblk _) ((h.mult _).trans (hker s)) _ (hW' _) X
    · exact pA_ad_c h.norm.atc hrc X
  intro γ hγ hbk

  have eA : ∀ g X, pA (adRep r g X) = repA r hblk g (pA X) := fun g X => pA_ad (hblk g) X
  have eA' : ∀ g Y, sA (repA r hblk g Y) = adRep r g (sA Y) := fun g Y => ad_sA (hblk g) Y
  have t1 : ∀ g v, Loc.colRep (Af.tw W 1) g v =
      ((if (r g).right = 1 then 1 else 1 : PadicAlgCl l) • wOf (r g)) *ᵥ v := fun g v => by
    rw [← hW', ite_self]
    exact congrArg (· *ᵥ v) (Af.tw_val W 1 g)
  have t2 : ∀ g v, Loc.colRep (Af.tw W θ) g v =
      ((if (r g).right = 1 then 1 else -1 : PadicAlgCl l) • wOf (r g)) *ᵥ v := fun g v => by
    rw [← hW', ← hθ]
    exact congrArg (· *ᵥ v) (Af.tw_val W θ g)
  have eB1 : ∀ g X, pB 1 (adRep r g X) = Loc.colRep (Af.tw W 1) g (pB 1 X) := fun g X => by
    rw [t1]; exact pB_ad (hblk g) 1 (by ring) X
  have eB1' : ∀ g v, sB 1 (Loc.colRep (Af.tw W 1) g v) = adRep r g (sB 1 v) := fun g v => by
    rw [t1]; exact ad_sB (hblk g) 1 (by ring) v
  have eB2 : ∀ g X, pB (-1) (adRep r g X) = Loc.colRep (Af.tw W θ) g (pB (-1) X) := fun g X => by
    rw [t2]; exact pB_ad (hblk g) (-1) (by ring) X
  have eB2' : ∀ g v, sB (-1) (Loc.colRep (Af.tw W θ) g v) = adRep r g (sB (-1) v) := fun g v => by
    rw [t2]; exact ad_sB (hblk g) (-1) (by ring) v
  have hblkz : ∀ g, IsBlockSL2Embedding (r0 D.η D.ΨQ g) := fun g => isBlock_reducible_three_dim _ _ g
  have eC : ∀ g X, pC (adRep r g X) = adRep (r0 D.η D.ΨQ) g (pC X) := fun g X => by
    refine (pC_ad (hblk g) X).trans (Eq.trans ?_ (ad_pC (hblkz g) X).symm)
    rw [h.mult g, unitaryThreeReflection_right]
  have eC' : ∀ g X, pC (adRep (r0 D.η D.ΨQ) g X) = adRep r g (pC X) := fun g X => by
    refine (pC_ad (hblkz g) X).trans (Eq.trans ?_ (ad_pC (hblk g) X).symm)
    rw [h.mult g, unitaryThreeReflection_right]
  obtain ⟨zA, bA⟩ := bk_map (adRep r) (repA r hblk) pA cont_pA eA hγ hbk
  obtain ⟨z1, b1⟩ := bk_map (adRep r) _ (pB 1) (cont_pB 1) eB1 hγ hbk
  obtain ⟨z2, b2⟩ := bk_map (adRep r) _ (pB (-1)) (cont_pB (-1)) eB2 hγ hbk
  obtain ⟨zC, bC⟩ := bk_map (adRep r) _ pC cont_pC eC hγ hbk
  obtain ⟨xA, hxA⟩ := (mem_coboundaries1 _ _).1 (hA _ zA bA)
  obtain ⟨x1, hx1⟩ := (mem_coboundaries1 _ _).1 (hB1 _ z1 b1)
  obtain ⟨x2, hx2⟩ := (mem_coboundaries1 _ _).1 (hB2 _ z2 b2)
  obtain ⟨xC, hxC⟩ := (mem_coboundaries1 _ _).1
    (bloch_kato_nonpositive_weight inp.toCohInp D 0 le_rfl _ zC (fun g => pC_mem (γ g)) bC)
  refine (mem_coboundaries1 _ _).2 ⟨sA xA + (2⁻¹ : PadicAlgCl l) • sB 1 x1 + (2⁻¹ : PadicAlgCl l) • sB (-1) x2 + pC xC, fun g => ?_⟩
  rw [decomp (2⁻¹ : PadicAlgCl l) (by norm_num) (γ g), hxA g, hx1 g, hx2 g, hxC g]
  simp only [map_sub, map_add, map_smul, eA', eB1', eB2', eC', smul_sub]
  abel
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem norm_lt_one_of_nonunit {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) (hb : ¬ IsUnit b) :
    ‖(b : PadicAlgCl l)‖ < 1 := by
  rcases eq_or_ne b 0 with rfl | h0
  · simp
  have h := UpperTheory.V.Base.normO l c.O b h0
  have hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
      IsDiscreteValuationRing.addVal_eq_top_iff]
    exact fun h => h.elim hb h0
  have hl : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have h1 := pow_lt_one₀ (by positivity) hl hv
  rw [← h] at h1
  by_contra hn
  exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))

private theorem isLocPt_toBar {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (x : R →ₐ[c.O] c.O) : IsLocPt (toBar x) := by
  intro y hy
  refine norm_lt_one_of_nonunit c (x y) fun hu => ?_
  have h2 : IsUnit (y - algebraMap c.O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap c.O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap c.O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

private theorem map_reducible_three_dim {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S) (η : G →* ℤˣ)
    (Ψ : G →* Rˣ) : (GG.map f).comp (r0 η Ψ) = r0 η ((Units.map f.toMonoidHom).comp Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor R (Ψ g) : Matrix (Fin 3) (Fin 3) R).map f = tor S (Units.map f.toMonoidHom (Ψ g))
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map f.toMonoidHom) (Ψ g) (wt1 i))

private theorem coboundary_of_mem_B1 {Γ κ : Type} [Group Γ] [CommRing κ] (r : Γ →* GG 3 κ)
    (γ : Γ → Matrix (Fin 3) (Fin 3) κ) (h : γ ∈ ReciprocityTheory.Gal.B1 (adRep r)) : ∃ X, γ = cob r X := by
  obtain ⟨m, rfl⟩ := h
  refine ⟨-m, funext fun g => ?_⟩
  show adRep r g m - m = -m - adRep r g (-m)
  rw [map_neg]
  abel

private theorem isPush_push {O Γ R κ : Type} [CommRing O] [Group Γ] [CommRing R] [Algebra O R] [CommRing κ]
    [Algebra O κ] (f : R →ₐ[O] κ) (r : Γ →* GG 3 R) : IsPush (f.comp (entAlg O r).val) r (push f r) :=
  fun g => ⟨rfl, fun a b => ⟨Algebra.subset_adjoin ⟨g, a, b, rfl⟩, rfl⟩⟩

theorem UpperTheory.V.Lit.KN.ptHyp_of :
    Lit.InpN → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {U : D.ULoc} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁), ∀ [IsCMField K] (ι : Qbar l ≃+* ℂ), Aut.AutB D ι g₁ → Aut.LemW D ι g₁ →
      ∀ x₀ : S.R →ₐ[c.O] c.O, IsBase D.η D.Ψ S.r.hom x₀ → PtHyp D.η S.r.hom x₀ := by
  intro hI Ω _ _ _ K _ _ _ l _ c N _ e ψ D U g₁ hM S _ ι hB hW x₀ hx
  have h0 : push (toBar x₀) S.r.hom = r0 D.η D.ΨQ := by
    have e1 : push (toBar x₀) S.r.hom =
        (GG.map (algebraMap c.O (PadicAlgCl l))).comp (push x₀ S.r.hom) := rfl
    rw [e1, show push x₀ S.r.hom = r0 D.η D.Ψ from hx, map_reducible_three_dim]
    rfl
  refine ⟨fun f hf hU hL => ?_, fun j hj F hF hw => ?_, fun f hf F hF => ?_⟩
  · rw [h0]
    exact pt_fixed hI.toCohInp D hM (isPt_push D hM S f hf) hU hL
  · have h1 := tanCoc_isBK hI.toCohInp D hM S F (hF ▸ isLocPt_toBar x₀)
    rw [hF, h0] at h1
    rw [h0]
    exact coboundary_of_mem_B1 _ _ (bloch_kato_nonpositive_weight hI.toCohInp D j hj _ h1.1 hw h1.2)
  · have h1 := tanCoc_isBK hI.toCohInp D hM S F (hF ▸ hf.1)
    rw [hF] at h1
    have hp := isPt_push D hM S f hf.1
    have hz : Af.BlochKatoSelmerVanishes l (adRep (push f S.r.hom)) := by
      rcases (twoPt_shape S D.gd.l_odd hM f hf).1 with h | h
      · exact bloch_kato_type_one hI.toCohInp hI.adK D hM hp ι h (hB U S _ _ hp.mult (isPush_push f _) h)
      · exact Lit.KN.blochKatoSelmer_adRep_vanishes_of_typeII_modular hI D hM hp ι h
          (hW U S _ _ (isPush_push f _) h (typeII_facts hI.toCohInp D hM hp h).1)
    exact coboundary_of_mem_B1 _ _ (hz _ h1.1 h1.2)
end
