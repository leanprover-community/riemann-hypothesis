import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix NNReal

namespace UpperTheory.V.Sd.Wc

def nu {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) : Valuation ℂ ℝ≥0 :=
  (NormedField.valuation (K := Qbar l)).comap ι.symm.toRingHom

theorem nu_apply {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (x : ℂ) : nu ι x = ‖ι.symm x‖₊ := rfl

def IsPos {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop :=
  (∀ x y, B y x = starRingEnd ℂ (B x y)) ∧ ∀ x, x ≠ 0 → 0 < (B x x).re

section Weight

open MvPolynomial

variable {I : Type} [Fintype I]

def act (g : I → GL (Fin 2) ℂ) (x : I × Fin 2 → ℂ) : I × Fin 2 → ℂ :=
  fun p => ∑ j, x (p.1, j) * (g p.1 : Matrix (Fin 2) (Fin 2) ℂ) j p.2

def sbs (g : I → GL (Fin 2) ℂ) : MvPolynomial (I × Fin 2) ℂ →ₐ[ℂ] MvPolynomial (I × Fin 2) ℂ :=
  aeval fun p => ∑ j, X (p.1, j) * C ((g p.1 : Matrix (Fin 2) (Fin 2) ℂ) j p.2)

omit [Fintype I] in
theorem eval_sbs (g : I → GL (Fin 2) ℂ) (x : I × Fin 2 → ℂ) (P : MvPolynomial (I × Fin 2) ℂ) :
    eval x (sbs g P) = eval (act g x) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sbs]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, hp]; simp [sbs, act]

omit [Fintype I] in
theorem act_one (x : I × Fin 2 → ℂ) : act 1 x = x := by
  funext p; obtain ⟨v, i⟩ := p; fin_cases i <;> simp [act]

omit [Fintype I] in
theorem act_mul (g h : I → GL (Fin 2) ℂ) (x : I × Fin 2 → ℂ) : act (g * h) x = act h (act g x) := by
  funext p; simp [act, Matrix.mul_apply, Fin.sum_univ_two]; ring

def Wt (n : I → ℕ) : Submodule ℂ (MvPolynomial (I × Fin 2) ℂ) where
  carrier := {P | ∀ (s : I → ℂ) (x : I × Fin 2 → ℂ), eval (fun p => s p.1 * x p) P = (∏ v, s v ^ n v) * eval x P}
  add_mem' h h' s x := by rw [map_add, map_add, h, h', mul_add]
  zero_mem' s x := by simp
  smul_mem' c P h s x := by rw [smul_eval, smul_eval, h]; ring

def detE (e : I → ℤ) : (I → GL (Fin 2) ℂ) →* ℂˣ where
  toFun g := ∏ v, Matrix.GeneralLinearGroup.det (g v) ^ e v
  map_one' := by simp
  map_mul' g h := by simp [mul_zpow, Finset.prod_mul_distrib]

theorem sbs_mem {n : I → ℕ} (g : I → GL (Fin 2) ℂ) {P : MvPolynomial (I × Fin 2) ℂ} (h : P ∈ Wt n) : sbs g P ∈ Wt n := by
  intro s x
  rw [eval_sbs, eval_sbs, ← h]
  congr 2
  funext p
  simp [act, mul_add, mul_assoc]

def wRep (n : I → ℕ) (e : I → ℤ) : Representation ℂ (I → GL (Fin 2) ℂ) (Wt n) where
  toFun g := (detE e g : ℂ) • (sbs g).toLinearMap.restrict fun _ h => sbs_mem g h
  map_one' := by
    refine LinearMap.ext fun P => Subtype.ext (MvPolynomial.funext fun x => ?_)
    change eval x ((detE e 1 : ℂ) • sbs 1 P.1) = eval x P.1
    rw [smul_eval, eval_sbs, act_one, map_one, Units.val_one, one_mul]
  map_mul' g h := by
    refine LinearMap.ext fun P => Subtype.ext (MvPolynomial.funext fun x => ?_)
    change eval x ((detE e (g * h) : ℂ) • sbs (g * h) P.1) = eval x ((detE e g : ℂ) • sbs g ((detE e h : ℂ) • sbs h P.1))
    rw [smul_eval, smul_eval, eval_sbs, eval_sbs, smul_eval, eval_sbs, act_mul, map_mul, Units.val_mul, mul_assoc]

theorem eval_wRep (n : I → ℕ) (e : I → ℤ) (g : I → GL (Fin 2) ℂ) (P : Wt n) (x : I × Fin 2 → ℂ) :
    eval x (wRep n e g P).1 = (detE e g : ℂ) * eval (act g x) P.1 := by
  change eval x ((detE e g : ℂ) • sbs g P.1) = _
  rw [smul_eval, eval_sbs]

def rowE (I : Type) : I × Fin 2 → ℂ := fun p => ![0, 1] p.2

def tc (n : I → ℕ) : Wt n →ₗ[ℂ] ℂ := (aeval (rowE I)).toLinearMap.comp (Wt n).subtype

theorem tc_apply (n : I → ℕ) (P : Wt n) : tc n P = eval (rowE I) P.1 := rfl

def eY (n : I → ℕ) : Wt n := ⟨∏ v, X (v, 1) ^ n v, fun s x => by simp [mul_pow, Finset.prod_mul_distrib]⟩

end Weight

section Abs

variable {Γ G W : Type} [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W]

def AF (j : Γ →* G) (R : Representation ℂ G W) : Submodule ℂ (G → W) where
  carrier := {f | ∀ γ g, f (j γ * g) = R (j γ) (f g)}
  add_mem' h h' γ g := by simp [h γ g, h' γ g]
  zero_mem' γ g := by simp
  smul_mem' c f h γ g := by simp [h γ g]

def psi (R : Representation ℂ G W) (t : W →ₗ[ℂ] ℂ) : (G → W) →ₗ[ℂ] (G → ℂ) where
  toFun f g := t (R g⁻¹ (f g))
  map_add' f f' := by funext g; simp
  map_smul' c f := by funext g; simp

theorem psi_apply (R : Representation ℂ G W) (t : W →ₗ[ℂ] ℂ) (f : G → W) (g : G) : psi R t f g = t (R g⁻¹ (f g)) := rfl

def stab (j : Γ →* G) (H : Subgroup G) (g : G) : Subgroup Γ := H.comap ((MulAut.conj g⁻¹).toMonoidHom.comp j)

theorem mem_stab {j : Γ →* G} {H : Subgroup G} {g : G} {γ : Γ} : γ ∈ stab j H g ↔ g⁻¹ * j γ * g ∈ H := by
  simp [stab]

end Abs

variable (F : Type) [Field F] [NumberField F]

abbrev GF : Type := GL (Fin 2) (Af F)

def zc : (Af F)ˣ →* GF F := Matrix.GeneralLinearGroup.scalar (Fin 2)

def ratU : Fˣ →* (Af F)ˣ := Units.map (algebraMap F (Af F)).toMonoidHom

variable {F}

def Kc (c : Pl F → ℕ) : Subgroup (GF F) := ⨅ w, (K1 w (c w)).comap (Matrix.GeneralLinearGroup.map (pLoc F w))

def Hc (c : Pl F → ℕ) : Subgroup (GF F) := Kc c ⊔ (zc F).range

section Sp

variable {W : Type} [AddCommGroup W] [Module ℂ W]

variable (W) in

def Cen (ω : (Af F)ˣ →* ℂˣ) : Submodule ℂ (GF F → W) where
  carrier := {f | ∀ z g, f (g * zc F z) = (ω z : ℂ) • f g}
  add_mem' h h' z g := by simp [h z g, h' z g]
  zero_mem' z g := by simp
  smul_mem' c f h z g := by simp only [Pi.smul_apply, h z g]; exact smul_comm _ _ _

def Sp (Q : DefQuat F) (R : Representation ℂ (GF F) W) (c : Pl F → ℕ) (ω : (Af F)ˣ →* ℂˣ) : Submodule ℂ (GF F → W) :=
  AF Q.toFin R ⊓ Hi.fixd (Hi.rtr ℂ (GF F) W) (Kc c) ⊓ Cen W ω

variable (W) in

def Hk (w : Pl F) (c : ℕ) : Module.End ℂ (GF F → W) := Uop w ((Hi.rtr ℂ (GF F) W).comp (locGL F 2 w)) c

end Sp

structure CC (c : Pl F → ℕ) (ω : (Af F)ˣ →* ℂˣ) (k : ℤ) : Prop where
  lev : ∀ z, zc F z ∈ Kc c → ω z = 1
  rat : ∀ x : Fˣ, (ω (ratU F x) : ℂ) = ∏ v : InfinitePlace F, v.embedding (x : F) ^ k

variable (F) in

structure LDat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) where

  pl : InfinitePlace F → Pl F

  em : ∀ v, (pl v).adicCompletion F →+* ℂ
  em_alg : ∀ v (x : F), em v (algebraMap F _ x) = v.embedding x
  le : ∀ v x, nu ι (em v x) ≤ 1 ↔ Valued.v x ≤ 1
  lt : ∀ v x, nu ι (em v x) < 1 ↔ Valued.v x < 1
  res : ∀ v x, Valued.v x = 1 → nu ι (em v x ^ (l - 1) - 1) < 1
  mem : ∀ v, ((l : ℕ) : 𝓞 F) ∈ (pl v).asIdeal
  inj : Function.Injective pl
  surj : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ v, pl v = w
  norm : ∀ v, normV (pl v) = l
  unif : ∀ v, Valued.v ((l : ℕ) : (pl v).adicCompletion F) = WithZero.exp (-1 : ℤ)
  embAt : ∀ (τ : F →+* Qbar l) (w : Pl F), EmbAt w τ ↔ pl (InfinitePlace.mk (ι.toRingHom.comp τ)) = w

namespace LDat

variable {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι)

def ea (v : InfinitePlace F) : Af F →+* ℂ := (D.em v).comp (pLoc F (D.pl v))

def gl : GF F →* (InfinitePlace F → GL (Fin 2) ℂ) := Pi.monoidHom fun v => Matrix.GeneralLinearGroup.map (D.ea v)

def R (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ) : Representation ℂ (GF F) (Wt n) := (wRep n e).comp D.gl

def Cmp (Q : DefQuat F) : Prop := ∀ v y, Q.jc v y = (Q.jf y).map (D.ea v)

open Classical in

def nz (e : InfinitePlace F → ℤ) (w : Pl F) : ℂ := ∏ v, if D.pl v = w then (l : ℂ) ^ (-e v) else 1

open Classical in

def uf (e : InfinitePlace F → ℤ) (w : Pl F) : ℂ :=
  ∏ v, if D.pl v = w then (v.embedding (Formalism.L2.Host.unif w : Fˣ) / (l : ℂ)) ^ e v else 1

def resplit (Q : DefQuat F) : DefQuat F :=
  { Q with
    jc := fun v => (D.ea v).mapMatrix.comp Q.jf.toRingHom
    jc_alg := fun v x => by
      have h : D.ea v (algebraMap F (Af F) x) = v.embedding x := D.em_alg v x
      ext i j
      simp [Matrix.algebraMap_matrix_apply, apply_ite (D.ea v), h] }


theorem Cmp.toInf {D : LDat F ι} {Q : DefQuat F} (h : D.Cmp Q) (γ : Q.Dˣ) : Q.toInf γ = D.gl (Q.toFin γ) :=
  funext fun v => Units.ext (h v γ)

end LDat

end UpperTheory.V.Sd.Wc
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V.Af
open scoped Matrix NNReal

namespace UpperTheory.V.Sd.Wc

def WtFin : Prop := ∀ (I : Type) [Fintype I] (n : I → ℕ), FiniteDimensional ℂ (Wt n)

def WtMon : Prop :=
  ∀ (I : Type) [Fintype I] (n : I → ℕ) (P : MvPolynomial (I × Fin 2) ℂ), P ∈ Wt n ↔ ∀ d ∈ P.support, ∀ v, d (v, 0) + d (v, 1) = n v

def WtIrr : Prop := ∀ (I : Type) [Fintype I] (n : I → ℕ) (e : I → ℤ), (wRep n e).IsIrreducible

def WtEmb : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (n : I → ℕ) (e : I → ℤ) (v : I) (lam : DomWeight 2), (n v : ℤ) = lam.w 0 - lam.w 1 → e v = lam.w 1 →
    ∃ f : nablaSq ℂ 2 lam →ₗ[ℂ] Wt n, f ≠ 0 ∧ ∀ g x, f (GlobalTheory.Branching.sqRep ℂ 2 lam g x) = wRep n e (Pi.mulSingle v g) (f x)

def WtInj : Prop :=
  ∀ (I : Type) [Fintype I] (n : I → ℕ) (P : Wt n) (N : ℕ), N ≠ 0 →
    (∀ a : I → ℕ, MvPolynomial.eval (fun p : I × Fin 2 => ![((N * a p.1 : ℕ) : ℂ), 1] p.2) P.1 = 0) → P = 0

def Gauss : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (σ : Type) (P : MvPolynomial σ ℂ),
    (P ≠ 0 → ∃ x₀ : σ → ℂ, (∀ p, nu ι (x₀ p) ≤ 1) ∧ MvPolynomial.eval x₀ P ≠ 0 ∧
      ∀ x : σ → ℂ, (∀ p, nu ι (x p) ≤ 1) → nu ι (MvPolynomial.eval x P) ≤ nu ι (MvPolynomial.eval x₀ P)) ∧
    ((∀ x : σ → ℂ, (∀ p, nu ι (x p) ≤ 1) → nu ι (MvPolynomial.eval x P) ≤ 1) → ∀ x y : σ → ℂ, (∀ p, nu ι (x p) ≤ 1) →
      (∀ p, nu ι (x p - y p) < 1) → nu ι (MvPolynomial.eval x P - MvPolynomial.eval y P) < 1)

def Unitarize : Prop :=
  ∀ (Γ W : Type) [Group Γ] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ Γ W),
    (∀ (f : W →ₗ[ℂ] ℂ) (x : W), ∃ C : ℝ, ∀ γ, ‖f (ρ γ x)‖ ≤ C) →
    ∃ B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ, IsPos B ∧ ∀ γ x y, B (ρ γ x) (ρ γ y) = B x y

def WtHerm : Prop :=
  ∀ (I : Type) [Fintype I] (n : I → ℕ) (e : I → ℤ) (Γ : Type) [Group Γ] (g : Γ →* (I → GL (Fin 2) ℂ)),
    (∃ C : ℝ, ∀ γ v i j, ‖(g γ v : Matrix (Fin 2) (Fin 2) ℂ) i j‖ ^ 2 ≤ C * ‖(g γ v : Matrix (Fin 2) (Fin 2) ℂ).det‖) →
    ∃ B : Wt n →ₗ⋆[ℂ] Wt n →ₗ[ℂ] ℂ, IsPos B ∧ ∀ γ x y, B (wRep n e (g γ) x) (wRep n e (g γ) y) =
      ((∏ v, ‖(g γ v : Matrix (Fin 2) (Fin 2) ℂ).det‖ ^ ((n v : ℤ) + 2 * e v) : ℝ) : ℂ) * B x y

def DSC : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (X J V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (Ψ : V →ₗ[ℂ] (X → ℂ)),
    Function.Injective Ψ → ∀ T : J → Module.End ℂ V, (∀ i j, T i * T j = T j * T i) →
    (∀ j v, (∀ x, nu ι (Ψ v x) ≤ 1) → ∀ x, nu ι (Ψ (T j v) x) ≤ 1) → (∀ j v, (∀ x, nu ι (Ψ v x) < 1) → ∀ x, nu ι (Ψ (T j v) x) < 1) →
    ∀ (f : V) (a : J → ℂ), (∀ x, nu ι (Ψ f x) ≤ 1) → (∃ x, nu ι (Ψ f x) = 1) → (∀ j, nu ι (a j) ≤ 1) →
    (∀ j x, nu ι (Ψ (T j f) x - a j * Ψ f x) < 1) →
    ∃ (h : V) (b : J → ℂ), h ≠ 0 ∧ (∀ j, T j h = b j • h) ∧ ∀ j, nu ι (b j - a j) < 1

def Lift : Prop :=
  ∀ (ν : Valuation ℂ ℝ≥0) (Γ G W : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] (j : Γ →* G) (H : Subgroup G) (χ : H →* ℂˣ)
    (R : Representation ℂ G W) (t : W →ₗ[ℂ] ℂ) (e : W) (C : Subgroup Γ),
    (∀ γ ∈ C, j γ ∈ Subgroup.center G ∧ ∃ h : j γ ∈ H, ∀ x, R (j γ) x = (χ ⟨_, h⟩ : ℂ) • x) →
    (∀ g, ν ((C.relIndex (stab j H g) : ℕ) : ℂ) = 1) →
    ∀ ψ : G → ℂ, (∀ γ g, ψ (j γ * g) = ψ g) → (∀ g (h : H), ν (ψ (g * h) - (χ h : ℂ) * t (R (h : G)⁻¹ e) * ψ g) < 1) →
    ∃ f ∈ AF j R, (∀ g (h : H), f (g * h) = (χ h : ℂ) • f g) ∧ ∀ g, ν (psi R t f g - ψ g) < 1

def ExChi : Prop :=
  ∀ (G Z : Type) [Group G] [Group Z] (K : Subgroup G) (ζ : Z →* G) (ω : Z →* ℂˣ), (∀ z, ζ z ∈ Subgroup.center G) → (∀ z, ζ z ∈ K → ω z = 1) →
    ∃ χ : ↥(K ⊔ ζ.range) →* ℂˣ, ∀ h : ↥(K ⊔ ζ.range), (∃ k ∈ K, ∃ z, (h : G) = k * ζ z) ∧ ∀ k ∈ K, ∀ z, (h : G) = k * ζ z → χ h = ω z

def InvMean : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (Γ Z K : Subgroup G), Z ≤ Subgroup.center G → IsClosed (Z : Set G) →
    IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ U ∈ nhds (1 : G), ∃ L : Subgroup G, IsOpen (L : Set G) ∧ (L : Set G) ⊆ U) →
    (∃ s : Finset G, ∀ g, ∃ γ ∈ Γ, ∃ x ∈ s, ∃ k ∈ K, g = γ * x * k) →
    (∀ g, ∃ s : Finset G, ∀ γ ∈ Γ, g⁻¹ * γ * g ∈ K ⊔ Z → ∃ x ∈ s, ∃ z ∈ Z, γ = x * z) →
    ∃ I : (G → ℝ) →ₗ[ℝ] ℝ, ∀ φ : G → ℝ, (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → (∀ z ∈ Z, ∀ g, φ (g * z) = φ g) →
      (∃ L : Subgroup G, IsOpen (L : Set G) ∧ ∀ k ∈ L, ∀ g, φ (g * k) = φ g) →
      (∀ h, I (fun g => φ (g * h)) = I φ) ∧ ((∀ g, 0 ≤ φ g) → φ ≠ 0 → 0 < I φ)

def IrrSub : Prop :=
  ∀ (G V J : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    GlobalTheory.PRep.IsSmooth ρ → ∀ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, IsPos B → (∀ g, ∃ δ : ℂ, ∀ x y, B (ρ g x) (ρ g y) = δ * B x y) →
    ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional ℂ (Hi.fixd ρ K) →
    ∀ T : J → Module.End ℂ V, (∀ j (U : Submodule ℂ V), (∀ g, ∀ x ∈ U, ρ g x ∈ U) → ∀ x ∈ U ⊓ Hi.fixd ρ K, T j x ∈ U ⊓ Hi.fixd ρ K) →
    ∀ (f : V) (b : J → ℂ), f ≠ 0 → f ∈ Hi.fixd ρ K → (∀ j, T j f = b j • f) →
    ∃ (τ : SmIrr G) (Φ : τ.V →ₗ[ℂ] V) (x : τ.V), (∀ g y, Φ (τ.ρ g y) = ρ g (Φ y)) ∧ Φ x ≠ 0 ∧ Φ x ∈ Hi.fixd ρ K ∧ ∀ j, T j (Φ x) = b j • Φ x

def KcTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    (∀ c : Pl F → ℕ, {w | c w ≠ 0}.Finite → IsOpen (Kc c : Set (GF F)) ∧ IsCompact (Kc c : Set (GF F))) ∧
    (∀ U ∈ nhds (1 : GF F), ∃ L : Subgroup (GF F), IsOpen (L : Set (GF F)) ∧ (L : Set (GF F)) ⊆ U) ∧
    (∀ z, zc F z ∈ Subgroup.center (GF F)) ∧ IsClosed ((zc F).range : Set (GF F)) ∧ Continuous (zc F) ∧
    ∀ (c : Pl F → ℕ) (w : Pl F), ∀ k ∈ K1 w (c w), locGL F 2 w k ∈ Kc c

def FixGlob : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V), GlobalTheory.PRep.IsSmooth ρ →
    ∀ (c : Pl F → ℕ) (x : V), (∀ w, x ∈ Hi.fixd (ρ.comp (locGL F 2 w)) (K1 w (c w))) → x ∈ Hi.fixd ρ (Kc c)

def HkReps : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : Pl F) (c : ℕ), ∃ (N : ℕ) (a : Fin N → GL (Fin 2) (w.adicCompletion F)),
    (c ≠ 0 → ∀ i, ∃ u : w.adicCompletionIntegers F, a i = aff (atFin w (unif w)) (u : w.adicCompletion F)) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V), ∀ x ∈ Hi.fixd ρ (K1 w c),
      Uop w ρ c x ∈ Hi.fixd ρ (K1 w c) ∧ Uop w ρ c x = ∑ i, ρ (a i) x

def HkComm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V) (c : Pl F → ℕ),
    ∀ x ∈ Hi.fixd ρ (Kc c), ∀ w, Uop w (ρ.comp (locGL F 2 w)) (c w) x ∈ Hi.fixd ρ (Kc c) ∧
      ∀ w', Uop w (ρ.comp (locGL F 2 w)) (c w) (Uop w' (ρ.comp (locGL F 2 w')) (c w') x) =
        Uop w' (ρ.comp (locGL F 2 w')) (c w') (Uop w (ρ.comp (locGL F 2 w)) (c w) x)

def ExL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), SplitL F l → Nonempty (LDat F ι)

open Classical in

def GlFacts : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι),
    (∀ c : Pl F → ℕ, (∀ v, c (D.pl v) = 1) →
      (∀ k ∈ Kc c, ∀ v, (∀ i j, nu ι ((D.gl k v : Matrix (Fin 2) (Fin 2) ℂ) i j) ≤ 1) ∧ nu ι ((D.gl k v : Matrix (Fin 2) (Fin 2) ℂ) 1 0) < 1 ∧
        nu ι ((D.gl k v : Matrix (Fin 2) (Fin 2) ℂ) 1 1 - 1) < 1 ∧ nu ι (D.gl k v : Matrix (Fin 2) (Fin 2) ℂ).det = 1 ∧
        nu ι ((D.gl k v : Matrix (Fin 2) (Fin 2) ℂ).det ^ (l - 1) - 1) < 1) ∧
      ∀ a : InfinitePlace F → ℕ, ∃ k ∈ Kc c, ∀ v, (D.gl k v : Matrix (Fin 2) (Fin 2) ℂ) = !![1, 0; ((l * a v : ℕ) : ℂ), 1]) ∧
    (∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ a, D.gl (locGL F 2 w a) = 1) ∧
    (∀ v a, D.gl (locGL F 2 (D.pl v) a) = Pi.mulSingle v (Matrix.GeneralLinearGroup.map (D.em v) a)) ∧
    (∀ (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ) z x,
      D.R n e (zc F z) x = (∏ v, D.ea v (z : Af F) ^ ((n v : ℤ) + 2 * e v)) • x) ∧
    (∀ e w, nu ι (D.uf e w) = 1) ∧
    ∀ e e' : InfinitePlace F → ℤ, (∀ v, ((l : ℤ) - 1) ∣ e' v - e v) → ∀ w, nu ι (D.uf e' w - D.uf e w) < 1

def NrdSq : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Q : DefQuat F) (y : Q.D), (Q.jf y).det ^ 2 = algebraMap F (Af F) (Algebra.norm F y)

def NormLow : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F) (f : Q.D →ₗ[F] F), ∃ C : ℝ,
    ∀ (v : InfinitePlace F) (y : Q.D), v (f y) ^ 4 ≤ C * v (Algebra.norm F y)

def Denom : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Q : DefQuat F) (f : Q.D →ₗ[F] F) (S : Set (Matrix (Fin 2) (Fin 2) (Af F))), IsCompact S →
    ∃ N : ℕ, N ≠ 0 ∧ ∀ y : Q.D, Q.jf y ∈ S → IsIntegral ℤ ((N : F) * f y)

def BoxFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F) (S : Set (Matrix (Fin 2) (Fin 2) (Af F))), IsCompact S →
    ∀ B : ℝ, {y : Q.D | Q.jf y ∈ S ∧ ∀ v : InfinitePlace F, v (Algebra.norm F y) ≤ B}.Finite

def ShortVec : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Q : DefQuat F), ∃ N : ℕ, N ≠ 0 ∧ ∀ g : GF F, ∃ γ : Q.Dˣ,
    (∀ i j, ((g⁻¹ * Q.toFin γ : GF F) : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈ Ohat F) ∧
    ∀ i j, (N : Af F) * (((Q.toFin γ)⁻¹ * g : GF F) : Matrix (Fin 2) (Fin 2) (Af F)) i j ∈ Ohat F

def ClassFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Q : DefQuat F) (K : Subgroup (GF F)), IsOpen (K : Set (GF F)) →
    ∃ s : Finset (GF F), ∀ g, ∃ γ : Q.Dˣ, ∃ x ∈ s, ∃ k ∈ K, g = Q.toFin γ * x * k

def StabFin : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F) (K : Subgroup (GF F)), IsCompact (K : Set (GF F)) →
    ∀ g, (Subgroup.center Q.Dˣ).relIndex (stab Q.toFin (K ⊔ (zc F).range) g) ≠ 0

def LocTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (u : Pl F) (c : ℕ), c ≠ 0 → normV u = 2 → ∀ k ∈ K1 u c, ∀ n : ℕ, Odd n →
    k ^ n ∈ Subgroup.center (GL (Fin 2) (u.adicCompletion F)) → k ∈ Subgroup.center (GL (Fin 2) (u.adicCompletion F))

def StabTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F),
    (∀ γ ∈ Subgroup.center Q.Dˣ, ∃ x : Fˣ, Q.toFin γ = zc F (ratU F x)) ∧ (∀ x : Fˣ, ∃ γ ∈ Subgroup.center Q.Dˣ, Q.toFin γ = zc F (ratU F x)) ∧
    ∀ c : Pl F → ℕ, {w | c w ≠ 0}.Finite → (∃ u, c u ≠ 0 ∧ normV u = 2) →
      ∀ g, ∃ a : ℕ, (Subgroup.center Q.Dˣ).relIndex (stab Q.toFin (Hc c) g) = 2 ^ a

def SpFacts : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Q : DefQuat F) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (R : Representation ℂ (GF F) W) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ ω : (Af F)ˣ →* ℂˣ,
    FiniteDimensional ℂ (Sp Q R c ω) ∧ ∀ f ∈ Sp Q R c ω, ∀ w, Hk W w (c w) f ∈ Sp Q R c ω ∧
      ∀ w', Hk W w (c w) (Hk W w' (c w') f) = Hk W w' (c w') (Hk W w (c w) f)

def CCof : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (Q : DefQuat F)
    (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ) (k : ℤ), (∀ v, (n v : ℤ) + 2 * e v = k) → ∀ c ω, ∀ f ∈ Sp Q (D.R n e) c ω, f ≠ 0 → CC c ω k

def PsiHk : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (c : Pl F → ℕ), (∀ v, c (D.pl v) = 1) →
    (∀ n e, ∀ f ∈ Hi.fixd (Hi.rtr ℂ (GF F) (Wt n)) (Kc c), psi (D.R n e) (tc n) f = 0 → f = 0) ∧
    ∀ w, ∃ (N : ℕ) (a : Fin N → GF F), ∀ n e, ∀ f ∈ Hi.fixd (Hi.rtr ℂ (GF F) (Wt n)) (Kc c), ∀ g,
      psi (D.R n e) (tc n) (D.nz e w • Hk (Wt n) w (c w) f) g = D.uf e w * ∑ i, psi (D.R n e) (tc n) f (g * a i)

def OrdT : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (Q : DefQuat F) (c : Pl F → ℕ),
    {w | c w ≠ 0}.Finite → (∀ v, c (D.pl v) = 1) → ∀ n e ω, ∀ f ∈ Sp Q (D.R n e) c ω, f ≠ 0 →
    (∀ v, ∃ b : ℂ, nu ι b = 1 ∧ D.nz e (D.pl v) • Hk (Wt n) (D.pl v) 1 f = b • f) →
    ∃ s : ℂ, (∀ g, nu ι (psi (D.R n e) (tc n) (s • f) g) ≤ 1) ∧ (∃ g, nu ι (psi (D.R n e) (tc n) (s • f) g) = 1) ∧
      ∀ g, ∀ k ∈ Kc c, nu ι (psi (D.R n e) (tc n) (s • f) (g * k) - (detE e (D.gl k⁻¹) : ℂ) * psi (D.R n e) (tc n) (s • f) g) < 1

def LiftD : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (Q : DefQuat F)
    (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → (∀ v, c (D.pl v) = 1) → (∃ u, c u ≠ 0 ∧ normV u = 2) →
    ∀ (n n' : InfinitePlace F → ℕ) (e e' : InfinitePlace F → ℤ) (k : ℤ), (∀ v, (n v : ℤ) + 2 * e v = k) → (∀ v, (n' v : ℤ) + 2 * e' v = k) →
    (∀ v, ((l : ℤ) - 1) ∣ e' v - e v) → ∀ ω, CC c ω k → ∀ f ∈ Sp Q (D.R n e) c ω,
    (∀ g, nu ι (psi (D.R n e) (tc n) f g) ≤ 1) → (∃ g, nu ι (psi (D.R n e) (tc n) f g) = 1) →
    (∀ g, ∀ k ∈ Kc c, nu ι (psi (D.R n e) (tc n) f (g * k) - (detE e (D.gl k⁻¹) : ℂ) * psi (D.R n e) (tc n) f g) < 1) →
    ∃ f' ∈ Sp Q (D.R n' e') c ω, ∀ g, nu ι (psi (D.R n' e') (tc n') f' g - psi (D.R n e) (tc n) f g) < 1

def CongD : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (Q : DefQuat F)
    (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → (∀ v, c (D.pl v) = 1) →
    ∀ (n n' : InfinitePlace F → ℕ) (e e' : InfinitePlace F → ℤ), (∀ v, ((l : ℤ) - 1) ∣ e' v - e v) → ∀ ω, ∀ f ∈ Sp Q (D.R n e) c ω,
    ∀ mu : Pl F → ℂ, (∀ w, Hk (Wt n) w (c w) f = mu w • f) →
    (∀ g, nu ι (psi (D.R n e) (tc n) f g) ≤ 1) → (∃ g, nu ι (psi (D.R n e) (tc n) f g) = 1) →
    ∀ f' ∈ Sp Q (D.R n' e') c ω, (∀ g, nu ι (psi (D.R n' e') (tc n') f' g - psi (D.R n e) (tc n) f g) < 1) →
    ∃ h ∈ Sp Q (D.R n' e') c ω, ∃ mu' : Pl F → ℂ, h ≠ 0 ∧ (∀ w, Hk (Wt n') w (c w) h = mu' w • h) ∧
      ∀ w, nu ι (D.nz e' w * mu' w - D.nz e w * mu w) < 1

def HermD : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (Q : DefQuat F)
    (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ) (k : ℤ), (∀ v, (n v : ℤ) + 2 * e v = k) → ∀ c ω, CC c ω k →
    ∃ B : Wt n →ₗ⋆[ℂ] Wt n →ₗ[ℂ] ℂ, IsPos B ∧ ∀ γ x y, B (D.R n e (Q.toFin γ) x) (D.R n e (Q.toFin γ) y) =
      ((‖(ω (Matrix.GeneralLinearGroup.det (Q.toFin γ)) : ℂ)‖ : ℝ) : ℂ) * B x y

def Peter : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F) (W : Type) [AddCommGroup W] [Module ℂ W]
    (R : Representation ℂ (GF F) W) (ω : (Af F)ˣ →* ℂˣ), IsOpen (ω.ker : Set (Af F)ˣ) →
    ∀ B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ, IsPos B → (∀ γ x y, B (R (Q.toFin γ) x) (R (Q.toFin γ) y) =
      ((‖(ω (Matrix.GeneralLinearGroup.det (Q.toFin γ)) : ℂ)‖ : ℝ) : ℂ) * B x y) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GF F) V), GlobalTheory.PRep.IsSmooth ρ →
    ∀ i : V →ₗ[ℂ] (GF F → W), Function.Injective i → (∀ h x g, i (ρ h x) g = i x (g * h)) → (∀ x, i x ∈ AF Q.toFin R ⊓ Cen W ω) →
    ∃ B' : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, IsPos B' ∧ ∀ g, ∃ δ : ℂ, ∀ x y, B' (ρ g x) (ρ g y) = δ * B' x y

def ToIrr : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Q : DefQuat F) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (R : Representation ℂ (GF F) W) (c : Pl F → ℕ), {w | c w ≠ 0}.Finite → ∀ ω : (Af F)ˣ →* ℂˣ,
    ∀ B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ, IsPos B → (∀ γ x y, B (R (Q.toFin γ) x) (R (Q.toFin γ) y) =
      ((‖(ω (Matrix.GeneralLinearGroup.det (Q.toFin γ)) : ℂ)‖ : ℝ) : ℂ) * B x y) →
    ∀ f ∈ Sp Q R c ω, f ≠ 0 → ∀ mu : Pl F → ℂ, (∀ w, Hk W w (c w) f = mu w • f) →
    ∃ (τ : SmIrr (GF F)) (Φ : τ.V →ₗ[ℂ] (GF F → W)) (x : τ.V), (∀ h y g, Φ (τ.ρ h y) g = Φ y (g * h)) ∧ (∀ y, Φ y ∈ AF Q.toFin R) ∧
      Φ x ≠ 0 ∧ Φ x ∈ Sp Q R c ω ∧ ∀ w, Hk W w (c w) (Φ x) = mu w • Φ x

def FinProj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2), π.IsRegAlg → ∃ τ : SmIrr (GF F), π.IsFinComp τ ∧
    ∀ x : π.V, x ≠ 0 → ∃ p : π.V →ₗ[ℂ] τ.V, p x ≠ 0 ∧ ∀ g y, p (π.finPart g y) = τ.ρ g (p y)

def CentChar : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2), ∃ ω : HChar F,
    (∀ (z : Ideles F), ∀ φ ∈ π.V, ∀ g, φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) ∧
    ∀ z x, π.finPart (zc F z) x = ((ω.1 (finId F z) : ℂˣ) : ℂ) • x

def PolGL2 : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (ω : HChar F),
    (∀ (z : Ideles F), ∀ φ ∈ π.V, ∀ g, φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) → π.IsSelfDualBy ω

def SignChar : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (k : ℤ),
    (∀ x : Fˣ, ((ω.1 (finId F (ratU F x)) : ℂˣ) : ℂ) = ∏ v : InfinitePlace F, v.embedding (x : F) ^ k) →
    ∀ v v' : InfinitePlace F, ω.locInf v (-1) = ω.locInf v' (-1)

def SatOfVec : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (π : TR.CuspSub F 2) (w : Pl F) (x : π.V) (mu z : ℂ), x ≠ 0 →
    x ∈ Hi.fixd (π.locRep w) (K1 w 0) → Uop w (π.locRep w) 0 x = mu • x →
    π.locRep w (Matrix.GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) x = z • x →
    ∃ B, π.HasSat w B ∧ (algSat 2 (normV w) B).sum = mu ∧ (algSat 2 (normV w) B).prod = (normV w : ℂ) * z

def ToD : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (Q : DefQuat F), D.Cmp Q →
    ∀ (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ) (π : TR.CuspSub F 2), π.IsRegAlg →
    (∀ v, π.HasInfChar v (infOf ![-e v, -e v - n v - 1])) → ∀ (c : Pl F → ℕ) (ω : (Af F)ˣ →* ℂˣ) (x : π.V) (mu : Pl F → ℂ), x ≠ 0 →
    (∀ w, x ∈ Hi.fixd (π.locRep w) (K1 w (c w)) ∧ Uop w (π.locRep w) (c w) x = mu w • x) → (∀ z, π.finPart (zc F z) x = (ω z : ℂ) • x) →
    ∃ f ∈ Sp Q (D.R n e) c ω, f ≠ 0 ∧ ∀ w, Hk (Wt n) w (c w) f = mu w • f

def FromD : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (D : LDat F ι) (Q : DefQuat F), D.Cmp Q →
    ∀ (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ), (∀ v, n v ≠ 0) → ∀ (c : Pl F → ℕ) (ω : (Af F)ˣ →* ℂˣ) (mu : Pl F → ℂ)
    (τ : SmIrr (GF F)) (Φ : τ.V →ₗ[ℂ] (GF F → Wt n)) (x : τ.V), (∀ h y g, Φ (τ.ρ h y) g = Φ y (g * h)) → (∀ y, Φ y ∈ AF Q.toFin (D.R n e)) →
    Φ x ≠ 0 → Φ x ∈ Sp Q (D.R n e) c ω → (∀ w, Hk (Wt n) w (c w) (Φ x) = mu w • Φ x) →
    ∃ (π : TR.CuspSub F 2) (y : π.V), (∀ v, π.HasInfChar v (infOf ![-e v, -e v - n v - 1])) ∧ y ≠ 0 ∧
      (∀ w, y ∈ Hi.fixd (π.locRep w) (K1 w (c w)) ∧ Uop w (π.locRep w) (c w) y = mu w • y) ∧ ∀ z, π.finPart (zc F z) y = (ω z : ℂ) • y

def WtOuter : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : InfinitePlace F → ℕ) (e : InfinitePlace F → ℤ), ∃ lam : InfinitePlace F → DomWeight 2,
    IsOuter lam (wRep n e) ∧ (∀ v, (lam v).w 0 = e v + n v ∧ (lam v).w 1 = e v) ∧
      ∀ v, (GlobalTheory.UnitaryBC.infOfWeight (lam v)).map Neg.neg = infOf ![-e v, -e v - n v - 1]

def GalCong : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r r' : G F Ω →* GL (Fin 2) (Qbar l)), Continuous r → Continuous r' →
    (∀ᶠ w : Pl F in Filter.cofinite, ∃ B B' : Multiset ℂ, B.card = 2 ∧ B'.card = 2 ∧ FrobEig ι r w B ∧ FrobEig ι r' w B' ∧
      nu ι (B'.sum - B.sum) < 1 ∧ B'.prod = B.prod) →
    Matrix.GeneralLinearGroup.det.comp r' = Matrix.GeneralLinearGroup.det.comp r ∧
      ∀ g i, ‖(r' g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.coeff i - (r g : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.coeff i‖ < 1

end UpperTheory.V.Sd.Wc
end
end
