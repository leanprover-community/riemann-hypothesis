import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValRat

section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem castGL_symm_bc {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin b) R) :
    (castGL h S).symm (bc f g) = bc f ((castGL h R).symm g) := by
  subst h; rfl

theorem castGL_bc {a b : ℕ} (h : a = b) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin a) R) :
    castGL h S (bc f g) = bc f (castGL h R g) := by
  subst h; rfl

theorem bc_comp {m : ℕ} {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) (x : GL (Fin m) R) :
    bc g (bc f x) = bc (g.comp f) x := by
  apply Units.ext; ext i j; rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ} {G : GAtP p}

def tPos (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : E →+* LL :=
  if Even s.val then tE (pos ⟨v, s⟩) else (tE (pos ⟨v, s⟩)).comp (σ : E →+* E)

theorem tPos_apply (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) (x : E) :
    tPos σ tE pos v s x = tE (pos ⟨v, s⟩) (if Even s.val then x else σ x) := by
  unfold tPos
  split_ifs <;> rfl

def blkLL (A : LocAt F E n G) (σ : E →ₐ[F] E) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (γ : GL (Fin n) E) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) : GL (Fin (G.P.m + 1)) LL :=
  bc (tPos σ tE pos v s) ((castGL A.rk E).symm (A.B⁻¹ * γ * A.B))

theorem gPos_act (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (e : LL →+* G.Kf) (hA : A.ActB)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (i : G.comp) (γ : (G.lev i).Γ) (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    gPosGL G.P v s ((G.lev i).act v γ) = Matrix.GeneralLinearGroup.map e (blkLL A σ tE pos (A.gamI i γ) v s) := by
  have h1 : (G.lev i).act v γ = bc (A.iw v) ((castGL A.rk E).symm (A.B⁻¹ * A.gamI i γ * A.B)) := by
    rw [← castGL_symm_bc, ← hA i v γ, MulEquiv.symm_apply_apply]
  rw [h1]
  apply Units.ext
  ext a b
  show G.P.ι v ((G.P.σ v ^ s.val) (A.iw v _)) = e (tPos σ tE pos v s _)
  rw [tPos_apply, hpos]

theorem actX_map (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (e : LL →+* G.Kf) (hA : A.ActB)
    (hpos : ∀ v (s : Fin (G.P.n' v)) (x : E),
      e (tE (pos ⟨v, s⟩) (if Even s.val then x else σ x)) = G.P.ι v ((G.P.σ v ^ s.val) (A.iw v x)))
    (i : G.comp) (γ : (G.lev i).Γ) (Q : XR G.P LL) :
    (G.lev i).actX γ (MvPolynomial.map e Q) =
      MvPolynomial.map e (natActR G.P LL (blkLL A σ tE pos (A.gamI i γ)) Q) := by
  unfold Level.actX
  rw [natAct_eq, map_natActR]
  congr 2
  funext v s
  exact gPos_act A tE pos e hA hpos i γ v s

def atInfGL (emb : Tau → E →+* ℂ) (γ : GL (Fin n) E) : Tau → GL (Fin n) ℂ := fun τ => bc (emb τ) γ

theorem unit_of_std {J : Matrix (Fin n) (Fin n) E} (B γ : GL (Fin n) E) (hB : cT (σ : E →+* E) B.1 * J * B.1 = 1)
    (hγ : γ ∈ UJ (σ : E →+* E) J) : cT (σ : E →+* E) (B⁻¹ * γ * B).1 * (B⁻¹ * γ * B).1 = 1 := by
  have h1 : cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * cT (σ : E →+* E) B.1 = 1 := by
    rw [← cT_mul, ← Units.val_mul, mul_inv_cancel]
    exact cT_one _
  have hJ : J = cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (B⁻¹ : GL (Fin n) E).1 := by
    calc J = (cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * cT (σ : E →+* E) B.1) * J * (B.1 * (B⁻¹ : GL (Fin n) E).1) := by
          rw [h1, ← Units.val_mul, mul_inv_cancel]
          simp
      _ = cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (cT (σ : E →+* E) B.1 * J * B.1) * (B⁻¹ : GL (Fin n) E).1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hB, Matrix.mul_one]
  have hγ' : cT (σ : E →+* E) γ.1 * J * γ.1 = J := hγ
  simp only [Units.val_mul, cT_mul]
  calc _ = cT (σ : E →+* E) B.1 * (cT (σ : E →+* E) γ.1 *
        (cT (σ : E →+* E) (B⁻¹ : GL (Fin n) E).1 * (B⁻¹ : GL (Fin n) E).1) * γ.1) * B.1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [← hJ, hγ', hB]

theorem blk_hAt (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (γ : GL (Fin n) E) (hU : cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 * (A.B⁻¹ * γ * A.B).1 = 1)
    (v : Fin G.P.nV) (s : Fin (G.P.n' v)) :
    Matrix.GeneralLinearGroup.map embLL (blkLL A σ tE pos γ v s) =
      hAt G.P A.rk pos (atInfGL emb A.B⁻¹) (atInfGL emb γ) v s := by
  have hM : atInfGL emb A.B⁻¹ (pos ⟨v, s⟩) * atInfGL emb γ (pos ⟨v, s⟩) * (atInfGL emb A.B⁻¹ (pos ⟨v, s⟩))⁻¹ =
      bc (emb (pos ⟨v, s⟩)) (A.B⁻¹ * γ * A.B) := by
    simp [atInfGL, map_mul, map_inv]
  unfold hAt
  rw [hM]
  apply Units.ext
  ext a b
  by_cases hs : Even s.val
  · simp only [hs, if_true]
    show embLL (tPos σ tE pos v s _) = emb (pos ⟨v, s⟩) _
    rw [tPos_apply, if_pos hs, htE]
    rfl
  · simp only [hs, if_false]
    have hinv : ((A.B⁻¹ * γ * A.B)⁻¹ : GL (Fin n) E).1 = cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 := by
      rw [Matrix.coe_units_inv]
      exact Matrix.inv_eq_left_inv hU
    show embLL (tPos σ tE pos v s _) =
      ((reG G.P A.rk (bc (emb (pos ⟨v, s⟩)) (A.B⁻¹ * γ * A.B)))⁻¹ : GL (Fin (G.P.m + 1)) ℂ).1 b a
    rw [tPos_apply, if_neg hs, htE, ← map_inv, ← map_inv]
    show _ = emb (pos ⟨v, s⟩) (((A.B⁻¹ * γ * A.B)⁻¹ : GL (Fin n) E).1 _ _)
    rw [hinv]
    rfl

theorem evC_blk (A : LocAt F E n G) (tE : Tau → E →+* LL) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
    (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (γ : GL (Fin n) E) (hU : cT (σ : E →+* E) (A.B⁻¹ * γ * A.B).1 * (A.B⁻¹ * γ * A.B).1 = 1)
    (Gm : Tau → Matrix (Fin n) (Fin n) ℂ)
    (z z' : Frames Gm) (hz : IsTr (atInf emb γ) z z') (Q : XR G.P LL) :
    evC G.P A.rk pos Gm (crdB emb A.B) (MvPolynomial.map embLL (natActR G.P LL (blkLL A σ tE pos γ) Q)) z' =
      evC G.P A.rk pos Gm (crdB emb A.B) (MvPolynomial.map embLL Q) z := by
  rw [map_natActR]
  have h1 : (fun v s => Matrix.GeneralLinearGroup.map embLL (blkLL A σ tE pos γ v s)) =
      hAt G.P A.rk pos (atInfGL emb A.B⁻¹) (atInfGL emb γ) := by
    funext v s
    exact blk_hAt A tE pos emb embLL htE γ hU v s
  rw [h1]
  exact evC_natAct G.P A.rk pos Gm (atInfGL emb A.B⁻¹) (atInfGL emb γ) z z' hz (MvPolynomial.map embLL Q)

end Formalism.L2.G.Cmp

end
end

section
noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

theorem colSpan_map {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A g : Matrix (Fin k) (Fin k) K) :
    (colSpan R g).map ((Matrix.mulVecLin A).restrictScalars R) = colSpan R (A * g) := by
  simp only [colSpan, Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prV_incl (w : HeightOneSpectrum (𝓞 F)) :
    (prV (E := E) w).comp (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) = inclE (F := F) (w.adicCompletion F) := by
  ext x
  simp [prV, inclE]

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ} {G : GAtP p}

theorem eQ_iw (A : LocAt F E n G) (v : Fin G.P.nV) :
    ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F)).comp (A.iw v) = A.phE v := by
  ext x
  simp [LocAt.iw]

private theorem bc_bc_eq_bc_comp {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] {m : ℕ}
    (φ : R₂ →+* R₃) (ψ : R₁ →+* R₂) (x : GL (Fin m) R₁) : bc φ (bc ψ x) = bc (φ.comp ψ) x := by
  ext i j
  simp [bc]

theorem LocAt.isPt_smul (A : LocAt F E n G) (hA : A.ActB) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (x κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : A.IsPt i g x) (γ : (G.lev i).Γ) (hκ : A.IsAway i γ κ) :
    A.IsPt i (fun v => (G.lev i).act v γ * g v)
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) * x * κ⁻¹) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hκ1, hκ2⟩ := hκ
  refine ⟨fun w hw => ?_, fun v => ?_⟩
  · simp only [map_mul, map_inv, hx1 w hw, hκ2 w hw]
    group
  · have hP : bc (A.ph v) (bc (prV (E := E) (A.pl v).1)
        (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ))) = bc (A.phE v) (A.gamI i γ) := by
      rw [bc_bc_eq_bc_comp, bc_bc_eq_bc_comp, RingHom.comp_assoc, prV_incl, LocAt.phE]
    have hQ : bc ((A.eQ v : G.P.Qq v →+* (A.pl v).1.adicCompletion F))
        (castGL A.rk (G.P.Qq v) ((G.lev i).act v γ)) =
          (bc (A.phE v) A.B)⁻¹ * bc (A.phE v) (A.gamI i γ) * bc (A.phE v) A.B := by
      rw [hA i v γ, bc_bc_eq_bc_comp, eQ_iw]
      simp only [map_mul, map_inv]
    simp only [map_mul, map_inv, hκ1 v, inv_one, mul_one, hP, hx2 v, hQ]
    group

theorem atInf_mul (emb : Tau → E →+* ℂ) (a b : Matrix (Fin n) (Fin n) E) (τ : Tau) :
    atInf emb (a * b) τ = atInf emb a τ * atInf emb b τ := by
  simp [atInf, Matrix.map_mul]

theorem CmpTie.val_equiv {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {embLL : LL →+* ℂ} {tE : Tau → E →+* LL}
    {e : LL →+* G.Kf} {A : LocAt F E n G} {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
    {V cls : Type} {embV : V → cls → Frames (gramC J emb) → ℂ} {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}
    {cmp : V → G.Fn} (K : CmpTie S emb embLL tE G e A pos embV yc cmp)
    (htE : ∀ τ x, embLL (tE τ x) = emb τ x) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : A.ActB)
    (x : V) (i : G.comp) (L : G.P.Tup) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hL : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)))
    (γ : (G.lev i).Γ) (hγ : A.gamI i γ ∈ UJ (σ : E →+* E) J) (κ : S.U) (hκ : A.IsAway i γ κ.1)
    (c : cls) (γ₀ : GL (Fin n) E) (hγ₀ : γ₀ ∈ UJ (σ : E →+* E) J) (κ₀ : S.U)
    (hpt : A.IsPt i g (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (yc c).1 * κ₀.1))
    (z z₁ z₂ : Frames (gramC J emb)) (h1 : IsTr (atInf emb (A.gamI i γ)) z₁ z) (h2 : IsTr (atInf emb γ₀) z₂ z₁) :
    (S.chi κ : ℂ) * evC G.P A.rk pos (gramC J emb) (crdB emb A.B)
        (MvPolynomial.map embLL (K.val x i ((G.lev i).smul γ L))) z =
      evC G.P A.rk pos (gramC J emb) (crdB emb A.B)
        (MvPolynomial.map embLL (natActR G.P LL (blkLL A σ tE pos (A.gamI i γ)) (K.val x i L))) z := by
  rw [evC_blk A tE pos emb embLL htE (A.gamI i γ) (unit_of_std A.B _ hBs hγ) (gramC J emb) z₁ z h1,
    K.val_emb x i L g hL c γ₀ hγ₀ κ₀ hpt z₁ z₂ h2]
  have hL' : ∀ v, (G.lev i).smul γ L v = colSpan (G.P.W v)
      (((G.lev i).act v γ * g v : GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
        Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
    intro v
    show (L v).map _ = _
    rw [hL v, colSpan_map]
    rfl
  have hpt' : A.IsPt i (fun v => (G.lev i).act v γ * g v)
      (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ * γ₀) * (yc c).1 * (κ₀ * κ⁻¹ : S.U).1) := by
    have := A.isPt_smul hA i g _ κ.1 hpt γ hκ
    have e1 : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ * γ₀) * (yc c).1 * (κ₀ * κ⁻¹ : S.U).1 =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (A.gamI i γ) *
          (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ₀ * (yc c).1 * κ₀.1) * (κ.1)⁻¹ := by
      rw [map_mul]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    rw [e1]
    exact this
  have h3 : IsTr (atInf emb ((A.gamI i γ * γ₀ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) z₂ z := by
    intro τ
    rw [h1 τ, h2 τ, ← Matrix.mul_assoc, Units.val_mul, atInf_mul]
  rw [K.val_emb x i _ _ hL' c (A.gamI i γ * γ₀) (Subgroup.mul_mem _ hγ hγ₀) (κ₀ * κ⁻¹) hpt' z z₂ h3, ← mul_assoc]
  congr 1
  rw [← Units.val_mul, ← map_mul]
  simp

end Formalism.L2.G.Cmp

end
end
