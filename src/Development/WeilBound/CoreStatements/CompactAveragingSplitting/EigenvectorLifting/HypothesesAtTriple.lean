import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.LocalDef
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasAd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift

section
noncomputable section

namespace PositivityTheory.ThK.PT

open scoped Matrix
open GlobalTheory.WeilM

section Forms

variable {k : Type} [Field k] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}

theorem map_mul_c {a b d : Type} [Fintype b] (A : Matrix a b K) (B : Matrix b d K) : (A * B).map c = A.map c * B.map c :=
  Matrix.map_mul (f := c.toRingHom)

theorem map_one_c {a : Type} [DecidableEq a] : (1 : Matrix a a K).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)

theorem exists_left_inv (hK : IsField K) {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] (C : Matrix a b K)
    (h : ∀ t, C *ᵥ t = 0 → t = 0) : ∃ L : Matrix b a K, L * C = 1 := by
  letI := hK.toField
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot'.2 fun t ht => h t ht)
  refine ⟨LinearMap.toMatrix' g, Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]

theorem isLagr_of_free [Invertible (2 : k)] (hK : IsField K) (hc : ∀ x, c (c x) = x) {N m : ℕ} (hN : N = 2 * m)
    {J : Matrix (Fin N) (Fin N) K} (hJ : IsSkewM c J) {Y : Matrix (Fin N) (Fin m) K} (hY : Yᵀ * J * Y.map c = 0)
    (hf : ∀ t, Y *ᵥ t = 0 → t = 0) : IsLagr c J Y := by
  obtain ⟨L, hL⟩ := exists_left_inv hK Y hf
  have cc : ∀ {a b : Type} (A : Matrix a b K), (A.map c).map c = A := fun A => Matrix.ext fun i j => hc _
  have hJ' : (J.map c)ᵀ = -J := Matrix.ext fun i j => hJ.1 i j
  have sk : ∀ {a b : Type} (A : Matrix (Fin N) a K) (B : Matrix (Fin N) b K),
      Bᵀ * J * A.map c = -((Aᵀ * J * B.map c).map c)ᵀ := fun A B => by
    rw [map_mul_c, map_mul_c, cc, Matrix.transpose_mul, Matrix.transpose_mul, hJ', Matrix.transpose_map,
      Matrix.transpose_transpose, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin N) (Fin m) K, Yᵀ * J * Z.map c = 1 := ⟨(J⁻¹ * Lᵀ).map c, by
    rw [cc, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hJ.2, ← Matrix.transpose_mul, hL, Matrix.transpose_one]⟩
  have hZ' : Zᵀ * J * Y.map c = -1 := by rw [sk, hZ, map_one_c, Matrix.transpose_one]
  set S := Zᵀ * J * Z.map c with hS
  have hS' : (S.map c)ᵀ = -S := by rw [hS, neg_eq_iff_eq_neg.2 (sk Z Z)]
  let t : Matrix (Fin m) (Fin m) K := -(⅟(2 : k) • Sᵀ)
  have ht : t.map c = ⅟(2 : k) • S := by
    ext i j
    have : c (S j i) = -S i j := congrFun (congrFun hS' i) j
    simp [t, this]
  have a1 : ∀ A B : Matrix (Fin N) (Fin m) K, (A + B).map c = A.map c + B.map c := fun A B =>
    Matrix.map_add _ (map_add c) _ _
  have e1 : Yᵀ * J * (Z + Y * t).map c = 1 := by
    rw [a1, map_mul_c, Matrix.mul_add, hZ, ← Matrix.mul_assoc, hY, Matrix.zero_mul, add_zero]
  have e2 : (Z + Y * t)ᵀ * J * Y.map c = -1 := by rw [sk, e1, map_one_c, Matrix.transpose_one]
  have e3 : (Z + Y * t)ᵀ * J * (Z + Y * t).map c = 0 := by
    rw [a1, map_mul_c, Matrix.mul_add, ← Matrix.mul_assoc, e2, ht, Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul,
      Matrix.transpose_mul, Matrix.mul_assoc tᵀ, Matrix.mul_assoc tᵀ, hZ, ← hS]
    simp only [t, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.mul_one, Matrix.neg_mul,
      Matrix.one_mul]
    rw [add_assoc, ← neg_add, ← add_smul, invOf_two_add_invOf_two, one_smul, add_neg_cancel]
  set X := Z + Y * t
  have g : (Matrix.fromCols Y X)ᵀ * J * (Matrix.fromCols Y X).map c = Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.transpose_fromCols, Matrix.fromCols_map, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, hY, e1, e2, e3]
  have g' : ((Matrix.fromBlocks 0 (-1) 1 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (((Matrix.fromCols Y X)ᵀ).map c * J.map c)) * Matrix.fromCols Y X = 1 := by
    have := congrArg (fun M => M.map c) g
    simp only [map_mul_c, cc] at this
    rw [Matrix.mul_assoc, this, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero c), map_one_c, Matrix.map_neg _ (map_neg c),
      map_one_c, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp
  exact ⟨hY, X, _, e3, (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp; omega))).1 g', g'⟩

def anti (K : Type) [CommRing K] (n : ℕ) : Matrix (Fin n) (Fin n) K := fun i j => if i.val + j.val + 1 = n then 1 else 0

variable (c) in

def HasAnti {n : ℕ} (J : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ P Q : Matrix (Fin n) (Fin n) K, P * Q = 1 ∧ Q * P = 1 ∧ Pᵀ * J * P.map c = anti K n



end Forms


end PositivityTheory.ThK.PT
end
end

section
noncomputable section

namespace PositivityTheory.ThK.PT

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (IsInertAt)
open Neutral.B1 (localIdele)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)}

theorem isField_Ev (hw : IsInertAt F E v w) : IsField (Ev E v) :=
  MulEquiv.isField (Field.toIsField _) (complEquiv hw ((under_eq_iff hw w).2 rfl)).toMulEquiv

theorem isQuad_Ev (hσ : IsCMExt F E σ) (v : Pl F) : ∃ ξ, IsQuad (cV σ v) ξ := by
  obtain ⟨δ, b, hδ, h0, h1, -⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hσ.2.2.1 (conj_conj hσ) (not_forall.1 (conj_ne hσ))
  refine ⟨inclR (F := F) (Fv F v) (b 1), (b.ne_zero 1).isUnit.map _, ?_, Algebra.TensorProduct.basis (Fv F v) b, ?_, ?_⟩
  · change inclR (F := F) (Fv F v) (σ (b 1)) = _
    rw [h1, map_neg]
  · rw [Algebra.TensorProduct.basis_apply, h0]; rfl
  · rw [Algebra.TensorProduct.basis_apply]; rfl

omit [NumberField E] in
theorem comp_cA (z : AE F E) : compFin F E v (cA σ z) = cV σ v (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] in
theorem comp_incl (x : E) : compFin F E v (inclR (F := F) (AF F) x) = inclR (F := F) (Fv F v) x :=
  congrArg (· ⊗ₜ[F] x) (map_one (evFin F v))


theorem psi_good {ψ : AddChar (AF F) ℂ} (h : IsStd ψ) (hu : PsiUnr ψ v) {ψv : AddChar (Fv F v) ℂ} (e : ∀ x, ψv x = psiLoc ψ v x) :
    Continuous ψv ∧ ψv ≠ 1 := by
  refine ⟨?_, fun h1 => ?_⟩
  · rw [show (ψv : _ → ℂ) = psiLoc ψ v from funext e]
    exact h.1.comp (continuous_const.prodMk (continuous_singleFin v))
  · obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (1 : ℤ))
    have := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((hu x).1 fun y _ => by rw [← e, h1]; rfl)
    rw [hx] at this
    exact absurd this (by decide)

theorem locIdele_spec (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) (y : (Ev E v)ˣ) :
    At (evFin F v) ((locIdele F w (Units.map (toCompl h).toMonoidHom y) : AE F E) - 1) ∧
      Units.map (compFin F E v).toMonoidHom (locIdele F w (Units.map (toCompl h).toMonoidHom y)) = y := by
  set x := Units.map (toCompl h).toMonoidHom y with hx
  have hf := finTens_locIdele (F := F) w x
  refine ⟨fun u hu => tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun P => ?_)),
    Units.ext ((toCompl_bijective hw h).1 ?_)⟩
  · rw [Algebra.smul_def, map_mul, map_sub, infTens_locIdele, map_one, sub_self, mul_zero, map_zero]
  · rw [Algebra.smul_def, map_mul, map_sub, map_one, map_mul, map_sub, hf, map_one, map_zero, map_zero]
    change (complMap rfl (u.2 (P.under (𝓞 F))) * algebraMap E _ 1) * (Neutral.B1.finiteSingle E w x.1 P - 1) = 0
    by_cases e : P = w
    · subst e
      subst h
      rw [show u.2 (P.under (𝓞 F)) = 0 from hu, map_zero, zero_mul, zero_mul]
    · rw [finSingle_ne e, sub_self, mul_zero]
  · have e1 := finAdEquiv_apply h (finTens F E (locIdele F w x))
    rw [hf] at e1
    have e2 : ∀ z : AE F E, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (finTens F E z) = compFin F E v z := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e2] at e1
    exact e1.symm.trans (finSingle_self w _)

theorem locChar_eq (hw : IsInertAt F E v w) (h : w.under (𝓞 F) = v) {χ : Chr F E} {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) (y : (Ev E v)ˣ) : χv y = χ (locIdele F w (Units.map (toCompl h).toMonoidHom y)) := by
  rw [← H _ (locIdele_spec hw h y).1, (locIdele_spec hw h y).2]

theorem continuous_loc (hw : IsInertAt F E v w) {χ : Chr F E} (hχ : Continuous χ) {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) : Continuous χv := by
  have h := (under_eq_iff hw w).2 rfl
  rw [show (χv : _ → Circle) = _ from funext (locChar_eq hw h H)]
  exact hχ.comp ((continuous_locIdele w).comp (Continuous.units_map _ (continuous_complEquiv hw h).1))

omit [NumberField E] in
theorem loc_algebraMap {χ : Chr F E} {χv : (Ev E v)ˣ →* Circle} (H : IsLocChar χ v χv) (a : (Fv F v)ˣ) :
    χv (Units.map (algebraMap (Fv F v) (Ev E v) : Fv F v →* Ev E v) a) =
      χ (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (localIdele F v a)) := by
  rw [← H]
  · congr 1
    exact Units.ext (congrArg (· ⊗ₜ[F] (1 : E)) (finSingle_self v _).symm)
  · intro u hu
    change u • (algebraMap (AF F) (AE F E) (localIdele F v a : (AF F)ˣ) - 1) = 0
    rw [← map_one (algebraMap (AF F) (AE F E)), ← map_sub, Algebra.smul_def, ← map_mul]
    refine (congrArg _ (Prod.ext ?_ (af_ext fun t => ?_))).trans (map_zero _)
    · change u.1 * (1 - 1) = 0
      rw [sub_self, mul_zero]
    · change u.2 t * (Neutral.B1.finiteSingle F v a.1 t - 1) = 0
      by_cases e : t = v
      · subst e
        rw [show u.2 t = 0 from hu, zero_mul]
      · rw [finSingle_ne e, sub_self, mul_zero]


theorem loc_eq_one (hw : IsInertAt F E v w) {χ : Chr F E} (hu : UnrAt χ w)
    (h1 : ∀ a, χ (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) a) = 1) {χv : (Ev E v)ˣ →* Circle}
    (H : IsLocChar χ v χv) : χv = 1 := MonoidHom.ext fun y => by
  have h := (under_eq_iff hw w).2 rfl
  have h0 : Valued.v (toCompl h y) ≠ 0 := (Valuation.ne_zero_iff _).2 (y.isUnit.map (toCompl h)).ne_zero
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (Valued.v (toCompl h y))
  have hx0 : x ≠ 0 := (Valuation.ne_zero_iff _).1 (hx ▸ h0)
  set s := Units.map (algebraMap (Fv F v) (Ev E v) : Fv F v →* Ev E v) (Units.mk0 x hx0) with hs
  have e1 : χv s = 1 := (loc_algebraMap H _).trans (h1 _)
  have e2 : Valued.v (toCompl h s) = Valued.v (toCompl h y) := by
    change Valued.v (toCompl h (x ⊗ₜ[F] 1)) = _
    rw [toCompl_tmul, map_one, mul_one, valued_complMap h hx0, isUnram_iff.1 (isUnram_of_isInertAt hw) w h, pow_one, hx]
  have e3 := hu (Units.map (toCompl h).toMonoidHom (y / s)) (by
    unfold Formalism.L2.Host.IsUnitAt
    rw [map_div, Units.val_div_eq_div_val, map_div₀]
    exact (div_eq_one_iff_eq (e2 ▸ h0)).2 e2.symm)
  have e4 : χv (y / s) = 1 := by
    rw [locChar_eq hw h H]
    exact Circle.ext (congrArg Units.val e3)
  rwa [map_div, e1, div_one] at e4


theorem det_loc {J : Matrix (Fin n) (Fin n) E} (h : IsUnit J.det) : IsUnit (locM (F := F) J v).det :=
  (RingHom.map_det (inclR (F := F) (Fv F v)) J) ▸ h.map _

theorem isHerm_loc {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsHerm σ B r s) : IsHerm (cV σ v) (locM X.J v) :=
  ⟨fun i j => congrArg (inclR (F := F) (Fv F v)) (hX.herm i j), det_loc (Vac.herm_det hX)⟩

theorem isSkew_loc {B : Base F E} {X : Spc F E n} {r s : ℕ} (hX : X.IsSkew σ B r s) : IsSkewM (cV σ v) (locM X.J v) :=
  ⟨fun i j => (congrArg (inclR (F := F) (Fv F v)) (hX.skew i j)).trans (map_neg _ _), det_loc (Vac.skew_det hX)⟩

theorem isLagr_loc [Invertible (2 : Fv F v)] {B : Base F E} (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) {W : Spc F E d} {r s : ℕ}
    (hW : W.IsSkew σ B r s) {m : ℕ} {Cy : Matrix (Fin d) (Fin m) (AE F E)} (hL : IsLagAt σ W v Cy) :
    IsLagr (cV σ v) (locM W.J v) (Cy.map (compFin F E v)) := by
  obtain ⟨ξ, hξ⟩ := isQuad_Ev hσ v
  refine isLagr_of_free (isField_Ev hw) hξ.invol hL.rank (isSkew_loc hW) ?_ fun t ht => ?_
  · have := congrArg (fun M => M.map (compFin F E v)) hL.iso
    simp only [Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at this
    have e1 : (incM F W.J).map (compFin F E v) = locM W.J v := Matrix.ext fun i j => comp_incl (F := F) (v := v) (W.J i j)
    have e2 : (Cy.map (cA σ)).map (compFin F E v) = (Cy.map (compFin F E v)).map (cV σ v) :=
      Matrix.ext fun i j => comp_cA (σ := σ) (v := v) (Cy i j)
    rwa [e1, e2, Matrix.transpose_map] at this
  · let t' : Fin m → AE F E := fun i => ThKH.Iwas.sgE E v (t i)
    have e : compFin F E v ∘ t' = t := funext fun i => ThKH.Iwas.comp_sgE _
    have ht' : At (evFin F v) t' := fun u hu => funext fun i => ThKH.Iwas.at_sgE _ u hu
    have := hL.free t' ht' (funext fun i => ThKH.Iwas.eq_zero_of_at
      (fun u hu => congrFun (ThKH.Iwas.at_mulVec_left hL.supp t' u hu) i) (by
        rw [RingHom.map_mulVec, e, ht]; rfl))
    rw [← e, this]
    exact funext fun i => map_zero _

end PositivityTheory.ThK.PT
end
end

section
noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (IsInertAt)

namespace PT

attribute [local instance] GlobalTheory.LocalData.complRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

local instance locField (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

local instance charZeroFv (v : Pl F) : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective

local instance invTwoFv (v : Pl F) : Invertible (2 : Fv F v) := invertibleOfNonzero two_ne_zero

local instance modTopEv (v : Pl F) : IsModuleTopology (Fv F v) (Ev E v) := ⟨rfl⟩

section Pair

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W} {v : Pl F}
  {ψv : AddChar (Fv F v) ℂ} {dv : Darboux (symp (R := Fv F v) (cV σ v) (-1) (locM X.J v) (locM W.J v)) (Fin n × Fin d)}
  {χXv χWv : (Ev E v)ˣ →* Circle} {omv : UG (cV σ v) (locM X.J v) × UG (cV σ v) (locM W.J v) →* Module.End ℂ (Fn F n d v)}
  (L : IsLocPair M ψ χX χW om v ψv dv χXv χWv omv)
include L

theorem actsW {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) {hv : UG (cV σ v) (locM W.J v)}
    (e : (mat h).map (compFin F E v) = hv.1.1) {φ} (hφ : φ ∈ SB _) (φ₁) :
    Acts (evFin F v) (om (1, h)) φ φ₁ ↔ φ₁ = omv.comp (MonoidHom.inr _ _) hv φ := by
  obtain ⟨g', h', e1, e2, H⟩ := L.loc 1 (one_mem_UAt X v) h hh
  obtain rfl : g' = 1 := Subtype.ext (Units.ext (e1.symm.trans (Matrix.map_one _ (map_zero _) (map_one _))))
  obtain rfl : h' = hv := Subtype.ext (Units.ext (e2.symm.trans e))
  exact H φ hφ φ₁

theorem actsX {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) {gv : UG (cV σ v) (locM X.J v)}
    (e : (mat g).map (compFin F E v) = gv.1.1) {φ} (hφ : φ ∈ SB _) (φ₁) :
    Acts (evFin F v) (om (g, 1)) φ φ₁ ↔ φ₁ = omv.comp (MonoidHom.inl _ _) gv φ := by
  obtain ⟨g', h', e1, e2, H⟩ := L.loc g hg 1 (one_mem_UAt W v)
  obtain rfl : h' = 1 := Subtype.ext (Units.ext (e2.symm.trans (Matrix.map_one _ (map_zero _) (map_one _))))
  obtain rfl : g' = gv := Subtype.ext (Units.ext (e1.symm.trans e))
  exact H φ hφ φ₁

theorem exW {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    ∃ hv : UG (cV σ v) (locM W.J v), (mat h).map (compFin F E v) = hv.1.1 := by
  obtain ⟨-, h', -, e2, -⟩ := L.loc 1 (one_mem_UAt X v) h hh
  exact ⟨h', e2⟩

theorem splA : IsSplitting (sbClass (Fv F v)) ψv dv (fun (g : UG (cV σ v) (locM X.J v)) x => g.1.1 * x)
    (omv.comp (MonoidHom.inl _ _)) := by
  obtain ⟨-, d', h2, hA, -⟩ := L.weil
  have r : ∀ w, dv.rho ψv w = d'.rho ψv wᵀ := fun w => by rw [Darboux.rho, Darboux.rho, h2]
  refine ⟨hA.pres, fun g w φ hφ => ?_, hA.adm⟩
  rw [r, hA.impl _ _ _ hφ, r, actB, Matrix.transpose_mul]


theorem isEv_of {m : ℕ} {Cy : Matrix (Fin d) (Fin m) (AE F E)} (hC : At (evFin F v) Cy) {l : Fn F n d v →ₗ[ℂ] ℂ}
    (hl : IsEvAt M ψ v Cy l) (h0 : ∃ φ ∈ SB _, l φ ≠ 0) : IsEv (cV σ v) ψv dv (Cy.map (compFin F E v)) l := by
  refine ⟨h0, fun z φ hφ => ?_⟩
  have e : (z.map (ThKH.Iwas.sgE E v) * Cyᵀ).map (compFin F E v) = z * (Cy.map (compFin F E v))ᵀ := by
    rw [Matrix.map_mul, Matrix.transpose_map]
    congr 1
    exact Matrix.ext fun i j => ThKH.Iwas.comp_sgE _
  rw [← e]
  exact hl _ φ hφ _ (L.Heisenberg₂ _ (ThKH.Iwas.at_mul_right _ (ThKH.Iwas.at_transpose hC)) φ hφ)



end Pair


variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {v : Pl F}
  {w : HeightOneSpectrum (𝓞 E)}

theorem exists_loc (h1 : LocPairEx) (hT : IsTriple B G X om om') (hw : IsInertAt F E v w) (hv : v ∉ X.T) :
    ∃ ψv χ dv omv dv' omv', IsLocPair G.M B.ψ X.β (X.β / X.α) om v ψv dv χ 1 omv ∧
      IsLocPair G.M' B.ψ X.α (X.α / X.β) om' v ψv dv' χ 1 omv' ∧ Continuous ψv ∧ ψv ≠ 1 ∧ Continuous χ := by
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨ψv, dv, χ, χ₁, omv, L⟩ := h1 F E σ _ _ B _ _ _ _ _ _ P hT.weil v
  obtain ⟨ψv', dv', χ', χ₁', omv', L'⟩ := h1 F E σ _ _ B _ _ _ _ _ _ P' hT.weil' v
  obtain rfl : ψv' = ψv := AddChar.ext _ _ fun x => (L'.psi x).trans (L.psi x).symm
  have hab : w ∉ above E (X.T : Set (Pl F)) := fun h => hv (under_eq_of_isInertAt hw ▸ h)
  have uα := hT.chars.unrα w hab
  have uβ := hT.chars.unrβ w hab
  have hres : ∀ t, X.β (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) t) =
      X.α (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) t) := fun t => Circle.ext (by
    rw [hT.chars.resα t, hT.chars.resβ t, neg_one_pow_congr (Nat.even_add.1 hT.geo.even)])
  have k1 : ∀ {μ}, IsLocChar (X.β / X.α) v μ → μ = 1 := fun H =>
    loc_eq_one hw (div_eq_mul_inv X.β X.α ▸ uβ.mul uα.inv) (fun t => by rw [MonoidHom.div_apply, hres, div_self']) H
  have k2 : ∀ {μ}, IsLocChar (X.α / X.β) v μ → μ = 1 := fun H =>
    loc_eq_one hw (div_eq_mul_inv X.α X.β ▸ uα.mul uβ.inv) (fun t => by rw [MonoidHom.div_apply, hres, div_self']) H
  obtain rfl := k1 L.chW
  obtain rfl := k2 L'.chW
  obtain rfl : χ = χ' := div_eq_one.1 (k1 fun z hz => by rw [MonoidHom.div_apply, MonoidHom.div_apply, L.chX z hz, L'.chX z hz])
  obtain ⟨c1, c2⟩ := psi_good hT.base.std (hT.base.inert v w hw).2.2 L.psi
  exact ⟨_, _, dv, omv, dv', omv', L, L', c1, c2, continuous_loc hw hT.chars.heckeβ.1 L.chX⟩



end PT


end PositivityTheory.ThK
end
end
