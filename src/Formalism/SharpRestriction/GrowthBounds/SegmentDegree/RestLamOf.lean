import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FiniteRestrictSupport
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SelIsComplRestrictSupport
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrameZeroStrictMono
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CoarseLabelFactorisation

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section LamAbs

variable {R : Type} [CommRing R] {F : Type} [Field F] {σ τ : Type} {J : ℕ}

theorem lam_prod_monomial {ι : Type} (s : Finset ι) (f : ι → τ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul]

abbrev lam_ph (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (j : Fin J) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval fun v => (X (g j v) : MvPolynomial τ R) ^ e j v

theorem lam_expand (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (y : Fin J → MvPolynomial σ R) :
    ∏ j, lam_ph g e j (y j) = ∑ m ∈ Fintype.piFinset (fun j => (y j).support),
      monomial (∑ j, imgMon (g j) (e j) (m j)) (∏ j, coeff (m j) (y j)) := by
  classical
  have h : ∀ j, lam_ph g e j (y j) = ∑ m ∈ (y j).support, monomial (imgMon (g j) (e j) m) (coeff m (y j)) := by
    intro j
    conv_lhs => rw [(y j).as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => aeval_pow_monomial _ _ _ _
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_univ_sum]
  exact Finset.sum_congr rfl fun m _ => lam_prod_monomial _ _ _

theorem lam_coeff (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : τ →₀ ℕ) (S : Fin J → Set (σ →₀ ℕ))
    (hinj : ∀ m m' : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S j) → (∀ j, m' j ∈ S j) →
      ∑ j, imgMon (g j) (e j) (m j) = ∑ j, imgMon (g j) (e j) (m' j) → m = m')
    (y : Fin J → MvPolynomial σ F) (hy : ∀ j, y j ∈ restrictSupport F (S j)) (s : Fin J → σ →₀ ℕ)
    (hs : ∀ j, s j ∈ S j) :
    coeff (l + ∑ j, imgMon (g j) (e j) (s j)) (monomial l (1 : F) * ∏ j, lam_ph g e j (y j)) =
      ∏ j, coeff (s j) (y j) := by
  classical
  rw [coeff_monomial_mul, one_mul, lam_expand, coeff_sum, Finset.sum_eq_single s]
  · rw [coeff_monomial, if_pos rfl]
  · intro m hm hne
    rw [coeff_monomial, if_neg]
    intro h
    apply hne
    refine hinj m s (fun j => ?_) hs h
    have := Fintype.mem_piFinset.mp hm j
    exact ((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hy j)) (Finset.mem_coe.mpr this)
  · intro hnot
    rw [coeff_monomial, if_pos rfl]
    rw [Fintype.mem_piFinset] at hnot
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    exact Finset.prod_eq_zero (Finset.mem_univ j) (MvPolynomial.notMem_support_iff.mp hj)

theorem lam_dual {I : Type} {M : Type} [AddCommGroup M] [Module F M] (u : I → M)
    (hu : LinearIndependent F u) :
    ∃ ψ : M →ₗ[F] (I →₀ F), (∀ a, ψ (u a) a = 1) ∧ ∀ a b, b ≠ a → ψ (u a) b = 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination F u)
    (LinearMap.ker_eq_bot.mpr hu)
  have h1 : ∀ a, ψ (u a) = Finsupp.single a 1 := by
    intro a
    have h2 : Finsupp.linearCombination F u (Finsupp.single a 1) = u a := by simp
    rw [← h2]
    exact congrArg (fun f => f (Finsupp.single a 1)) hψ
  refine ⟨ψ, fun a => by rw [h1]; simp, fun a b hb => by rw [h1, Finsupp.single_apply, if_neg hb.symm]⟩

theorem lam_li_fixed (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : τ →₀ ℕ) (S : Fin J → Set (σ →₀ ℕ))
    (hinj : ∀ m m' : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S j) → (∀ j, m' j ∈ S j) →
      ∑ j, imgMon (g j) (e j) (m j) = ∑ j, imgMon (g j) (e j) (m' j) → m = m')
    {I : Fin J → Type} [∀ j, Fintype (I j)] (u : ∀ j, I j → MvPolynomial σ F)
    (hu : ∀ j, LinearIndependent F (u j)) (hS : ∀ j i, u j i ∈ restrictSupport F (S j)) :
    LinearIndependent F fun a : ∀ j, I j => monomial l (1 : F) * ∏ j, lam_ph g e j (u j (a j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have hstar : ∀ s : Fin J → σ →₀ ℕ, ∑ a, c a * ∏ j, coeff (s j) (u j (a j)) = 0 := by
    intro s
    by_cases hs : ∀ j, s j ∈ S j
    · have h1 := congrArg (coeff (l + ∑ j, imgMon (g j) (e j) (s j))) hc
      rw [coeff_sum, coeff_zero] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [coeff_smul, lam_coeff g e l S hinj (fun j => u j (a j)) (fun j => hS j (a j)) s hs, smul_eq_mul]
    · push Not at hs
      obtain ⟨j0, hj0⟩ := hs
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [Finset.prod_eq_zero (Finset.mem_univ j0) (li_coeff_zero (hS j0 (a j0)) hj0), mul_zero]
  choose ψ hψ using fun j => lam_dual (u j) (hu j)
  let supp : ∀ j, Finset (σ →₀ ℕ) := fun j => Finset.univ.biUnion fun a => (u j a).support
  let w : ∀ j, (σ →₀ ℕ) → F := fun j m => ψ j (monomial m 1) (b j)
  have hexp : ∀ j (a : I j), (ψ j (u j a)) (b j) = ∑ m ∈ supp j, coeff m (u j a) * w j m := by
    intro j a
    conv_lhs => rw [(u j a).as_sum]
    rw [map_sum, Finsupp.finsetSum_apply]
    have hsub : (u j a).support ⊆ supp j := fun m hm => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hm⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m _ => ?_
      have : (monomial m (coeff m (u j a)) : MvPolynomial σ F) = coeff m (u j a) • monomial m (1 : F) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro m _ hm
      rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]
  have h1 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = c b := by
    rw [Finset.sum_eq_single b]
    · rw [Finset.prod_eq_one fun j _ => (hψ j).1 (b j), mul_one]
    · intro a _ hab
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
      rw [Finset.prod_eq_zero (Finset.mem_univ j) ((hψ j).2 (a j) (b j) hj.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = 0 := by
    have e1 : ∀ a : ∀ j, I j, c a * ∏ j, (ψ j (u j (a j))) (b j) =
        ∑ s ∈ Fintype.piFinset supp, (c a * ∏ j, coeff (s j) (u j (a j))) * ∏ j, w j (s j) := by
      intro a
      rw [Finset.prod_congr rfl fun j _ => hexp j (a j), Finset.prod_univ_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.prod_mul_distrib, mul_assoc]
    rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← Finset.sum_mul, hstar s, zero_mul]
  rw [← h1, h2]

theorem lam_li_all {Φ : Type} (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : Φ → τ →₀ ℕ)
    (S : Φ → Fin J → Set (σ →₀ ℕ)) (I : Φ → Fin J → Type) [∀ f j, Fintype (I f j)]
    (u : ∀ f j, I f j → MvPolynomial σ F) (hu : ∀ f j, LinearIndependent F (u f j))
    (hS : ∀ f j i, u f j i ∈ restrictSupport F (S f j))
    (hinj : ∀ f f' (m m' : Fin J → σ →₀ ℕ), (∀ j, m j ∈ S f j) → (∀ j, m' j ∈ S f' j) →
      l f + ∑ j, imgMon (g j) (e j) (m j) = l f' + ∑ j, imgMon (g j) (e j) (m' j) → f = f' ∧ m = m') :
    LinearIndependent F fun x : (Σ f, ∀ j, I f j) =>
      monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j)) := by
  classical
  refine li_graded _ (fun x => x.1)
    (fun f => {n | ∃ m : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S f j) ∧ n = l f + ∑ j, imgMon (g j) (e j) (m j)}) ?_ ?_ ?_
  · rintro k k' n ⟨m, hm, rfl⟩ ⟨m', hm', h⟩
    exact (hinj k k' m m' hm hm' h).1
  · intro x
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    have hn' : coeff n (monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j))) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
    rw [coeff_monomial_mul'] at hn'
    split_ifs at hn' with hle
    · rw [one_mul, lam_expand, coeff_sum] at hn'
      obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
      rw [coeff_monomial] at hm0
      split_ifs at hm0 with heq
      · refine ⟨m, fun j => ?_, ?_⟩
        · exact ((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hS x.1 j (x.2 j)))
            (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · rw [heq]; exact (add_tsub_cancel_of_le hle).symm
      · exact absurd rfl hm0
    · exact absurd rfl hn'
  · intro k
    have hfix := lam_li_fixed g e (l k) (S k)
      (fun m m' hm hm' h => (hinj k k m m' hm hm' (by rw [h])).2) (u k) (hu k) (hS k)
    have hι : Function.Injective
        (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j)) := by
      rintro ⟨⟨f, a⟩, h⟩ ⟨⟨f', a'⟩, h'⟩ hxx
      simp only at h h'
      subst h
      subst h'
      simp only at hxx
      rw [hxx]
    have hcomp := hfix.comp _ hι
    have heq : (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} =>
        monomial (l x.1.1) (1 : F) * ∏ j, lam_ph g e j (u x.1.1 j (x.1.2 j))) =
        ((fun a : ∀ j, I k j => monomial (l k) (1 : F) * ∏ j, lam_ph g e j (u k j (a j))) ∘
          fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j)) := by
      funext x
      obtain ⟨⟨f, a⟩, h⟩ := x
      simp only at h
      subst h
      rfl
    rw [heq]
    exact hcomp

end LamAbs

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def lamG : Fin X.F.J → ℤ × Fin (r + K) → Fin n' × Fin (r + K) := fun _ v => (posOf n' v.1, v.2)

def lamE : Fin X.F.J → ℤ × Fin (r + K) → ℕ := fun j v => p ^ (X.F.dist (j.val : ℤ) v.1 + X.Rj p K (j.val : ℤ))

omit [NeZero n'] in

def lamL (la : Fin n' → Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => la v.1 v.2

def lamS (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) :
    Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {m | (∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) ∧
    m ∈ segDegSet (r := r) K (X.bfam p K la e (j.val : ℤ)) ∧ m ∈ X.resSet p K (j.val : ℤ)}

end Dat

def RestLamA : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → ∀ (j : ℤ) (b : ℤ → ℕ),
    (∀ x, x ∉ X.F.letters j → b x = 0) →
    ∃ y : Fin (Module.finrank O (X.Mj p K O j b)) → SegRing O r K, (∀ i, y i ∈ X.Mj p K O j b) ∧
      LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (y i)

def RestLamInj (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, ∀ la' ∈ X.LA p K, ∀ e' ∈ X.EE p K la',
    ∀ m m' : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) → (∀ j, m' j ∈ X.lamS p K la' e' j) →
      Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) =
        Dat.lamL K la' + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m' j) → (la = la' ∧ e = e') ∧ m = m'

def RestLamDeg (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, X.IsCLabel p K (Dat.lamL K la) ∧
    ∀ m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) →
      ∀ t, ∑ c : Fin (r + K), (Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (t, c) = X.a' p K t

theorem lam_map_phc {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r)
    (p K : ℕ) (j : Fin X.F.J) (P : SegRing R r K) :
    MvPolynomial.map f (X.phc p K R (j.val : ℤ) P) = lam_ph (X.lamG K) (X.lamE p K) j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Dat.phc, lam_ph]
  | add u v hu hv => simp only [map_add, hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [Dat.phc, lam_ph, Dat.lamG, Dat.lamE]

theorem lam_mem_lamS {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K] (O : Type) [CommRing O]
    (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) {y : SegRing O r K}
    (hy : y ∈ X.Mj p K O (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))) : y ∈ restrictSupport O (X.lamS p K la e j) := by
  classical
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  have hs := XX'_supported O X.F (j.val : ℤ) _ _ _ h1
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' : m ∈ y.support := Finset.mem_coe.mp hm
  refine ⟨fun v hv => ?_, (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h2 hm,
    (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h3 hm⟩
  have hvars : v ∈ y.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨m, hm', Finsupp.mem_support_iff.mpr hv⟩
  exact (MvPolynomial.mem_supported.mp hs) (Finset.mem_coe.mpr hvars)

theorem restLam_of_rests (C₀ : ℝ) (hA : RestLamA) (hI : RestLamInj C₀) (hD : RestLamDeg C₀) : RestLam C₀ := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX hLa hk
  classical
  let SS := (X.LA p K).sigma fun la => X.EE p K la
  let Φ := {x // x ∈ SS}
  have hΦ : ∀ f : Φ, f.1.1 ∈ X.LA p K ∧ f.1.2 ∈ X.EE p K f.1.1 := fun f => Finset.mem_sigma.mp f.2
  let nn : Φ → Fin X.F.J → ℕ := fun f j =>
    Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ)))
  have hex := fun (f : Φ) (j : Fin X.F.J) => hA p n' r K X O Sd hX (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ))
    (fun x hx => by simp [Dat.bfam, hx])
  choose y hyM hyL using hex
  set res := MvPolynomial.map (σ := ℤ × Fin (r + K)) (IsLocalRing.residue O) with hres
  have hli := lam_li_all (F := FF O) (X.lamG K) (X.lamE p K) (fun f : Φ => Dat.lamL K f.1.1)
    (fun f j => X.lamS p K f.1.1 f.1.2 j) (fun f j => Fin (nn f j)) (fun f j i => res (y f j i))
    (fun f j => hyL f j)
    (fun f j i => map_mem_restrictSupport _ _ (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j i)))
    (by
      intro f f' m m' hm hm' h
      obtain ⟨⟨h1, h2⟩, h3⟩ := hI p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2 f'.1.1 (hΦ f').1 f'.1.2 (hΦ f').2
        m m' hm hm' h
      refine ⟨Subtype.ext ?_, h3⟩
      obtain ⟨⟨la, e⟩, hf⟩ := f
      obtain ⟨⟨la', e'⟩, hf'⟩ := f'
      simp only at h1 h2
      subst h1
      subst h2
      rfl)

  have hmem : ∀ x : (Σ f : Φ, ∀ j, Fin (nn f j)),
      monomial (Dat.lamL K x.1.1.1) (1 : FF O) * ∏ j, lam_ph (X.lamG K) (X.lamE p K) j (res (y x.1 j (x.2 j))) ∈
        X.LamBar p K O := by
    rintro ⟨f, a⟩
    let Yf : Fin X.F.J → SegRing O r K := fun i => y f i (a i)
    let y' : ℤ → SegRing O r K := fun j => if h : 0 ≤ j ∧ j.toNat < X.F.J then Yf ⟨j.toNat, h.2⟩ else 0
    have hy'i : ∀ i : Fin X.F.J, y' (i.val : ℤ) = Yf i := by
      intro i
      have h : 0 ≤ (i.val : ℤ) ∧ ((i.val : ℤ)).toNat < X.F.J := ⟨by positivity, by simpa using i.isLt⟩
      simp only [y', dif_pos h]
      exact congrArg Yf (Fin.ext (by simp))
    obtain ⟨hlab, hdeg⟩ := hD p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2
    have hprod : (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) =
        ∏ j : Fin X.F.J, lam_ph (R := O) (X.lamG K) (X.lamE p K) j (Yf j) := by
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hy'i]
      rfl
    refine Submodule.subset_span ⟨(∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) *
      monomial (Dat.lamL K f.1.1) 1, ⟨fun j => X.bfam p K f.1.1 f.1.2 j, y', Dat.lamL K f.1.1, ?_, hlab, rfl, ?_⟩, ?_⟩
    · intro j
      by_cases h : 0 ≤ j ∧ j.toNat < X.F.J
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
        have hk' : k < X.F.J := by simpa using h.2
        have := hy'i ⟨k, hk'⟩
        simp only at this
        rw [this]
        exact hyM f ⟨k, hk'⟩ (a ⟨k, hk'⟩)
      · simp only [y', dif_neg h]
        exact Submodule.zero_mem _
    · rw [hprod, lam_expand]
      unfold RRdeg
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro n hn
      have hn' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
      rw [mul_comm, coeff_monomial_mul'] at hn'
      split_ifs at hn' with hle
      · rw [one_mul, coeff_sum] at hn'
        obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
        rw [coeff_monomial] at hm0
        split_ifs at hm0 with heq
        · have hn2 : n = Dat.lamL K f.1.1 + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) := by
            rw [heq]; exact (add_tsub_cancel_of_le hle).symm
          intro t
          rw [hn2]
          refine hdeg m (fun j => ?_) t
          exact (MvPolynomial.mem_restrictSupport_iff (R := O)).mp
            (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j (a j))) (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · exact absurd rfl hm0
      · exact absurd rfl hn'
    · rw [map_mul, map_monomial, map_one, mul_comm, Finset.prod_range, map_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [lam_map_phc, hy'i]
  have hfin : Module.Finite (FF O) (X.LamBar p K O) := by
    have := finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) (X.a' p K))
    refine Submodule.finiteDimensional_of_le
      (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.a' p K t}) ?_
    unfold Dat.LamBar
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨_, _, _, -, -, -, h⟩ := hg
    exact map_mem_restrictSupport _ _ h
  have hli' : LinearIndependent (FF O) (fun x : (Σ f : Φ, ∀ j, Fin (nn f j)) =>
      (⟨_, hmem x⟩ : X.LamBar p K O)) := by
    refine LinearIndependent.of_comp (X.LamBar p K O).subtype ?_
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  refine le_trans (le_of_eq ?_) hcard
  rw [Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_fin]
  rw [← Finset.sum_sigma (X.LA p K) (fun la => X.EE p K la)
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))]
  exact (Finset.sum_coe_sort SS
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))).symm

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem lam_sat_restrict {O σ : Type} [CommRing O] [IsDomain O] (s : Set (σ →₀ ℕ)) (f : MvPolynomial σ O) (a : O)
    (ha : a ≠ 0) (h : a • f ∈ restrictSupport O s) : f ∈ restrictSupport O s := by
  rw [MvPolynomial.mem_restrictSupport_iff] at h ⊢
  intro m hm
  apply h
  have hm' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hm)
  refine Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr ?_)
  rw [coeff_smul, smul_eq_mul]
  exact mul_ne_zero ha hm'

theorem lam_dvd_of_res {O σ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (P : MvPolynomial σ O) (h : MvPolynomial.map (IsLocalRing.residue O) P = 0) :
    ∃ z : MvPolynomial σ O, P = ϖ • z := by
  have hd : C ϖ ∣ P := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h1 : IsLocalRing.residue O (coeff m P) = 0 := by
      rw [← MvPolynomial.coeff_map, h, coeff_zero]
    rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨z, hz⟩ := hd
  exact ⟨z, by rw [hz, smul_eq_C_mul]⟩

theorem restLamA_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestLamA := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX j b hb
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have hsatX := (h12 p O Sd n' r K X.F X.L₁ X.N₁ j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) hX.valid hNK
    (fun _ => by positivity)).2.2.1
  have hsat : ∀ (f : SegRing O r K) (a : O), a ≠ 0 → a • f ∈ X.Mj p K O j b → f ∈ X.Mj p K O j b := by
    intro f a ha h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨⟨hsatX f a ha h1, lam_sat_restrict _ f a ha h2⟩, lam_sat_restrict _ f a ha h3⟩
  have hfin : Module.Finite O (X.Mj p K O j b) := restFin p n' r K X O j b hb
  have hfree : Module.Free O (X.Mj p K O j b) := Module.free_of_finite_type_torsion_free'
  let bs := Module.finBasis O (X.Mj p K O j b)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine ⟨fun i => (bs i : SegRing O r K), fun i => (bs i).2, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro cb hcb i
  choose c hc using fun i => IsLocalRing.residue_surjective (cb i)
  have h1 : MvPolynomial.map (IsLocalRing.residue O) (∑ i, c i • (bs i : SegRing O r K)) = 0 := by
    rw [sel_red_sum, ← hcb]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]
  obtain ⟨z, hz⟩ := lam_dvd_of_res hϖ _ h1
  have hzM : z ∈ X.Mj p K O j b := by
    refine hsat z ϖ hϖ.ne_zero ?_
    rw [← hz]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bs i).2
  have h2 : ∑ i, c i • bs i = ϖ • (⟨z, hzM⟩ : X.Mj p K O j b) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact hz
  have h3 := congrArg (fun v => bs.repr v i) h2
  simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
  rw [← hc i, h3, map_mul]
  have : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hϖ.not_isUnit
  rw [this, zero_mul]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

structure LamGeo {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  U1 : ∀ j j' : Fin X.F.J, ∀ x ∈ X.toLate (j.val : ℤ), ∀ x' ∈ X.toLate (j'.val : ℤ), posOf n' x = posOf n' x' →
    j = j' ∧ x = x'
  U2 : ∀ j j' : Fin X.F.J, ∀ x ∈ X.F.letters (j.val : ℤ), X.F.IsW (j.val : ℤ) x → ∀ x' ∈ X.F.letters (j'.val : ℤ),
    X.F.IsW (j'.val : ℤ) x' → posOf n' x = posOf n' x' → j = j' ∧ x = x'
  LK : ∀ j j' : Fin X.F.J, ∀ x ∈ X.F.letters (j.val : ℤ), X.F.IsW (j.val : ℤ) x → ∀ x' ∈ X.toLate (j'.val : ℤ),
    posOf n' x = posOf n' x' → (∃ i < r, x' = X.F.fr (j'.val : ℤ) i) ∧
      X.Pz p K (j.val : ℤ) x = X.Pz p K (j'.val : ℤ) x' * X.Qc p K (j'.val : ℤ)
  EX : ∀ t ∈ X.F.TT, ∃ j : Fin X.F.J, ∃ x ∈ X.toLate (j.val : ℤ), posOf n' x = t

def RestLamGeo (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    LamGeo X p K

def RestLamTau : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K →
    ∀ (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (i : Fin r),
      X.bfam p K la e (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val) = e j i

theorem lam_digit {P la la' A A' : ℕ} (h1 : la < P) (h2 : la' < P) (h : la + P * A = la' + P * A') :
    la = la' ∧ A = A' := by
  have hP : 0 < P := lt_of_le_of_lt (Nat.zero_le _) h1
  have e1 : (la + P * A) % P = la := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have e2 : (la' + P * A') % P = la' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  have hla : la = la' := by rw [← e1, ← e2, h]
  refine ⟨hla, ?_⟩
  subst hla
  have h3 : P * A = P * A' := by omega
  exact Nat.eq_of_mul_eq_mul_left hP h3

section Eval

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

theorem lam_img_apply (j : Fin X.F.J) (m : ℤ × Fin (r + K) →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) (t : Fin n') (c : Fin (r + K)) :
    imgMon (X.lamG K j) (X.lamE p K j) m (t, c) =
      ∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = t then X.Pz p K (j.val : ℤ) x * m (x, c) else 0 := by
  classical
  unfold imgMon
  rw [Finsupp.sum_apply]
  have hsub : m.support ⊆ X.F.letters (j.val : ℤ) ×ˢ (Finset.univ : Finset (Fin (r + K))) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨(hm v (Finsupp.mem_support_iff.mp hv)).1, Finset.mem_univ _⟩
  rw [Finsupp.sum_of_support_subset m hsub _ (by intro v _; simp), Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finsupp.single_apply, Dat.lamG, Prod.mk.injEq]
  by_cases h : posOf n' x = t
  · simp [h, Dat.lamE, Dat.Pz]
  · simp [h]

open Classical in

def segmentWeightExponent (m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ)) (t : Fin n') (c : Fin (r + K)) : ℕ :=
  ∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
    if posOf n' x = t then m j (x, c) else 0

theorem lam_eval (hG : LamGeo X p K) (m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ))
    (hm : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) (j0 : Fin X.F.J) (x0 : ℤ) (hx0 : x0 ∈ X.toLate (j0.val : ℤ))
    (c : Fin (r + K)) :
    (∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (posOf n' x0, c) =
      X.Pz p K (j0.val : ℤ) x0 * (m j0 (x0, c) + X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c) := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_congr rfl fun j _ => lam_img_apply X p K j (m j) (hm j) _ c]
  have hsplit : ∀ j : Fin X.F.J,
      (∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      (∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
        if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) +
      ∑ x ∈ X.toLate (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0 := by
    intro j
    unfold Dat.toLate
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
  have hlate : (∑ j : Fin X.F.J, ∑ x ∈ X.toLate (j.val : ℤ),
      if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      X.Pz p K (j0.val : ℤ) x0 * m j0 (x0, c) := by
    rw [Finset.sum_eq_single j0]
    · rw [Finset.sum_eq_single x0]
      · rw [if_pos rfl]
      · intro x hx hne
        rw [if_neg]
        intro h
        exact hne (hG.U1 j0 j0 x hx x0 hx0 h).2
      · intro h; exact absurd hx0 h
    · intro j _ hne
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [if_neg]
      intro h
      exact hne (hG.U1 j j0 x hx x0 hx0 h).1
    · intro h; exact absurd (Finset.mem_univ _) h
  have hW : (∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
      if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      X.Pz p K (j0.val : ℤ) x0 * (X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c) := by
    unfold segmentWeightExponent
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
    split_ifs with h
    · rw [(hG.LK j j0 x hxl hxW x0 hx0 h).2]; ring
    · simp
  rw [hlate, hW]; ring

end Eval

theorem restLamInj_of (C₀ : ℝ) (hGeo : RestLamGeo C₀) (hTau : RestLamTau) : RestLamInj C₀ := by
  intro p n' r K _ _ _ X hX hLa hk la hla e he la' hla' e' he' m m' hm hm' heq
  classical
  have hG := hGeo p n' r K X hX hLa hk
  have hok : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm j).1
  have hok' : ∀ j v, m' j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm' j).1
  have hlaS := Fintype.mem_piFinset.mp hla
  have hlaS' := Fintype.mem_piFinset.mp hla'

  have hdec : ∀ (j0 : Fin X.F.J) (x0 : ℤ), x0 ∈ X.toLate (j0.val : ℤ) → ∀ c : Fin (r + K),
      la (posOf n' x0) c = la' (posOf n' x0) c ∧ m j0 (x0, c) = m' j0 (x0, c) ∧
        segmentWeightExponent X K m (posOf n' x0) c = segmentWeightExponent X K m' (posOf n' x0) c := by
    intro j0 x0 hx0 c
    have h1 := congrArg (fun f => f (posOf n' x0, c)) heq
    simp only [Finsupp.add_apply] at h1
    rw [lam_eval X p K hG m hok j0 x0 hx0 c, lam_eval X p K hG m' hok' j0 x0 hx0 c] at h1
    have hl1 : la (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0 :=
      ((Finset.mem_filter.mp (hlaS (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c
    have hl2 : la' (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0 :=
      ((Finset.mem_filter.mp (hlaS' (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c
    obtain ⟨g1, g2⟩ := lam_digit hl1 hl2 h1
    refine ⟨g1, ?_⟩
    by_cases hfc : (∃ i < r, x0 = X.F.fr (j0.val : ℤ) i) ∧ c.val < r
    · obtain ⟨⟨i, hi, rfl⟩, hc⟩ := hfc
      have hcc : c = Fin.castAdd K ⟨c.val, hc⟩ := Fin.ext rfl
      have a1 : m j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ) := by
        rw [hcc]; exact (hm j0).2.2 i hi ⟨c.val, hc⟩
      have a2 : m' j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ) := by
        rw [hcc]; exact (hm' j0).2.2 i hi ⟨c.val, hc⟩
      exact lam_digit a1 a2 g2
    · have hw0 : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j v, mm j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) →
          segmentWeightExponent X K mm (posOf n' x0) c = 0 := by
        intro mm hmm
        unfold segmentWeightExponent
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x hx => ?_
        obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
        split_ifs with h
        · by_contra hne
          apply hfc
          refine ⟨(hG.LK j j0 x hxl hxW x0 hx0 h).1, ?_⟩
          by_contra hc
          exact (hmm j (x, c) hne).2 (not_lt.mp hc) hxW
        · rfl
      rw [hw0 m hok, hw0 m' hok'] at g2 ⊢
      simp only [mul_zero, add_zero] at g2
      exact ⟨g2, rfl⟩
  have hlaeq : la = la' := by
    funext t c
    by_cases ht : t ∈ X.F.TT
    · obtain ⟨j0, x0, hx0, rfl⟩ := hG.EX t ht
      exact (hdec j0 x0 hx0 c).1
    · have ha : X.a' p K t = 0 := by
        unfold Dat.a' Dat.d
        rw [if_neg ht]; simp
      have b1 := (Finset.mem_filter.mp (hlaS t)).2.1
      have b2 := (Finset.mem_filter.mp (hlaS' t)).2.1
      rw [ha] at b1 b2
      have c1 := Finset.single_le_sum (f := fun c => la t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have c2 := Finset.single_le_sum (f := fun c => la' t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
  have hmeq : m = m' := by
    funext j
    ext v
    obtain ⟨x, c⟩ := v
    by_cases hv : (x, c) ∈ okVars X.F K (j.val : ℤ)
    · by_cases hW : X.F.IsW (j.val : ℤ) x
      · have hTT : posOf n' x ∈ X.F.TT := by
          have := hv.1
          unfold Frames.letters at this
          exact (Finset.mem_filter.mp this).2
        obtain ⟨j0, x0, hx0, hpos⟩ := hG.EX _ hTT
        have h3 := (hdec j0 x0 hx0 c).2.2
        have hwv : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), segmentWeightExponent X K mm (posOf n' x0) c = mm j (x, c) := by
          intro mm
          unfold segmentWeightExponent
          rw [Finset.sum_eq_single j]
          · rw [Finset.sum_eq_single x]
            · rw [if_pos hpos.symm]
            · intro y hy hne
              obtain ⟨hyl, hyW⟩ := Finset.mem_filter.mp hy
              rw [if_neg]
              intro h
              exact hne (hG.U2 j j y hyl hyW x hv.1 hW (h.trans hpos)).2
            · intro h; exact absurd (Finset.mem_filter.mpr ⟨hv.1, hW⟩) h
          · intro j' _ hne
            refine Finset.sum_eq_zero fun y hy => ?_
            obtain ⟨hyl, hyW⟩ := Finset.mem_filter.mp hy
            rw [if_neg]
            intro h
            exact hne (hG.U2 j' j y hyl hyW x hv.1 hW (h.trans hpos)).1
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hwv m, hwv m'] at h3
        exact h3
      · exact (hdec j x (Finset.mem_filter.mpr ⟨hv.1, hW⟩) c).2.1
    · have z1 : m j (x, c) = 0 := by
        by_contra h; exact hv (hok j _ h)
      have z2 : m' j (x, c) = 0 := by
        by_contra h; exact hv (hok' j _ h)
      rw [z1, z2]
  refine ⟨⟨hlaeq, ?_⟩, hmeq⟩
  funext j i
  have d1 := (hm j).2.1 (X.F.fr (j.val : ℤ) i.val)
  have d2 := (hm' j).2.1 (X.F.fr (j.val : ℤ) i.val)
  rw [hTau p n' r K X hX] at d1 d2
  rw [← d1, ← d2, hmeq]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem lam_m_zero {a b m J : ℤ} (ha : 0 ≤ a) (ha' : a < J) (hb : 0 ≤ b) (hb' : b < J) (h : b = a + m * J) :
    m = 0 := by
  subst h
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have : m * J ≤ -J := by nlinarith
    omega
  · exact hm
  · have : J ≤ m * J := by nlinarith
    omega

private theorem fr_le_fr_of_index_le {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁)
    (j : ℤ) : ∀ k, k < r → ∀ i ≤ k, F.fr j i ≤ F.fr j k := by
  intro k
  induction k with
  | zero =>
    intro _ i hi
    have : i = 0 := by omega
    subst this
    exact le_refl _
  | succ k ih =>
    intro hk i hi
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · have h1 := ih (by omega) i (by omega)
      have h2 := hV.2.2.1 j k hk
      omega
    · have : i = k + 1 := by omega
      subst this
      exact le_refl _

private theorem exists_index_eq_fr_of_between {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁)
    (j x : ℤ) (hx : posOf n' x ∈ F.TT) :
    ∀ k, k < r → F.fr j 0 ≤ x → x ≤ F.fr j k → ∃ i ≤ k, x = F.fr j i := by
  intro k
  induction k with
  | zero =>
    intro _ h1 h2
    exact ⟨0, le_refl _, le_antisymm h2 h1⟩
  | succ k ih =>
    intro hk h1 h2
    rcases le_or_gt x (F.fr j k) with h | h
    · obtain ⟨i, hi, hxi⟩ := ih (by omega) h1 h
      exact ⟨i, by omega, hxi⟩
    · rcases lt_or_eq_of_le h2 with h' | h'
      · exact absurd hx (hV.2.2.2.2.2.1 j k x hk h h')
      · exact ⟨k + 1, le_refl _, h'⟩

theorem lam_W_late {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j x : ℤ)
    (hx : x ∈ X.F.letters j) (hW : X.F.IsW j x) : x ∈ X.toLate (j - 1) ∧ ∃ i < r, x = X.F.fr (j - 1) i := by
  classical
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hx1, hx2⟩, hxT⟩ := hx
  have hW' : x ≤ X.F.fr (j - 1) (r - 1) := hW
  obtain ⟨i, hi, rfl⟩ := exists_index_eq_fr_of_between X.F hV (j - 1) x hxT (r - 1) (by omega) hx1 hW'
  refine ⟨?_, i, by omega, rfl⟩
  have hg := hV.2.2.2.1 (j - 1 - 1)
  have h1 : j - 1 - 1 + 1 = j - 1 := by ring
  rw [h1] at hg
  have hm0 := fr_le_fr_of_index_le X.F hV (j - 1 - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
  have hmi := fr_le_fr_of_index_le X.F hV (j - 1) (r - 1) (by omega) i hi
  have hm0i := fr_le_fr_of_index_le X.F hV (j - 1) i (by omega) 0 (Nat.zero_le _)
  unfold Dat.toLate
  simp only [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hmi⟩, hxT⟩
  · unfold Frames.IsW
    omega

private theorem fr_last_lt_fr_last_succ {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (a : ℤ) : F.fr a (r - 1) < F.fr (a + 1) (r - 1) := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := hV.2.2.2.1 a
  have h2 := fr_le_fr_of_index_le F hV (a + 1) (r - 1) (by omega) 0 (Nat.zero_le _)
  omega

private theorem fr_last_le_fr_last_add_nat {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (a : ℤ) : ∀ k : ℕ, F.fr a (r - 1) ≤ F.fr (a + k) (r - 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h := fr_last_lt_fr_last_succ F hV (a + k)
    push_cast
    rw [← add_assoc]
    omega

private theorem fr_last_monotone {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (a b : ℤ) (h : a ≤ b) : F.fr a (r - 1) ≤ F.fr b (r - 1) := by
  have h1 := fr_last_le_fr_last_add_nat F hV a (b - a).toNat
  rw [Int.toNat_of_nonneg (by omega), show a + (b - a) = b by ring] at h1
  exact h1

private theorem eq_of_mod_eq_of_mem_Ioc_fr_last {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (s a b x x' : ℤ) (hsa : s ≤ a) (haJ : a < s + F.J) (hsb : s ≤ b)
    (hbJ : b < s + F.J) (hx1 : F.fr (a - 1) (r - 1) < x) (hx2 : x ≤ F.fr a (r - 1))
    (hx1' : F.fr (b - 1) (r - 1) < x') (hx2' : x' ≤ F.fr b (r - 1))
    (hp : x % (n' : ℤ) = x' % (n' : ℤ)) : a = b ∧ x = x' := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hper := hV.2.1 (s - 1) (r - 1)
  rw [show s - 1 + (F.J : ℤ) = s + F.J - 1 by ring] at hper
  have m1 := fr_last_monotone F hV (s - 1) (a - 1) (by omega)
  have m2 := fr_last_monotone F hV a (s + F.J - 1) (by omega)
  have m3 := fr_last_monotone F hV (s - 1) (b - 1) (by omega)
  have m4 := fr_last_monotone F hV b (s + F.J - 1) (by omega)
  have e1 : x % (n' : ℤ) + n' * (x / n') = x := by rw [Int.emod_def]; ring
  have e2 : x' % (n' : ℤ) + n' * (x' / n') = x' := by rw [Int.emod_def]; ring
  have hq := lam_m_zero (a := x - F.fr (s - 1) (r - 1) - 1) (b := x' - F.fr (s - 1) (r - 1) - 1)
    (m := x' / n' - x / n') (J := n') (by omega) (by omega) (by omega) (by omega)
    (by linear_combination e1 - e2 - hp)
  have hxx : x = x' := by
    have hq' : x' / (n' : ℤ) = x / n' := by linarith
    rw [hq'] at e2
    linarith
  refine ⟨?_, hxx⟩
  subst hxx
  rcases lt_trichotomy a b with h | h | h
  · have := fr_last_monotone F hV a (b - 1) (by omega)
    omega
  · exact h
  · have := fr_last_monotone F hV b (a - 1) (by omega)
    omega

private theorem mem_Ioc_and_posOf_mem_of_mem_late {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) (h : x ∈ X.toLate j) :
    X.F.fr (j - 1) (r - 1) < x ∧ x ≤ X.F.fr j (r - 1) ∧ posOf n' x ∈ X.F.TT := by
  classical
  unfold Dat.toLate at h
  simp only [Finset.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  unfold Frames.letters at h1
  simp only [Finset.mem_filter, Finset.mem_Icc] at h1
  unfold Frames.IsW at h2
  exact ⟨by omega, h1.1.2, h1.2⟩

private theorem mem_late_of_mem_Ioc_of_posOf_mem {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ}
    (hV : X.F.Valid L₁ N₁) (j x : ℤ) (h1 : X.F.fr (j - 1) (r - 1) < x) (h2 : x ≤ X.F.fr j (r - 1))
    (h3 : posOf n' x ∈ X.F.TT) : x ∈ X.toLate j := by
  classical
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h0 := fr_le_fr_of_index_le X.F hV (j - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
  unfold Dat.toLate
  simp only [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, h2⟩, h3⟩
  · unfold Frames.IsW
    omega

private theorem emod_eq_of_posOf_eq' {n' : ℕ} [NeZero n'] {x x' : ℤ} (h : posOf n' x = posOf n' x') :
    x % (n' : ℤ) = x' % (n' : ℤ) := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  unfold posOf at h
  have h' := congrArg Fin.val h
  simp only at h'
  clear h
  have a1 := Int.emod_nonneg x (ne_of_gt hn)
  have a2 := Int.emod_lt_of_pos x hn
  have b1 := Int.emod_nonneg x' (ne_of_gt hn)
  have b2 := Int.emod_lt_of_pos x' hn
  generalize x % (n' : ℤ) = u at *
  generalize x' % (n' : ℤ) = v at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
  omega

private theorem nat_log_div_pow_eq_sub (p N : ℕ) : ∀ d : ℕ, Nat.log p (N / p ^ d) = Nat.log p N - d := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.log_div_base, ih]
    omega

private theorem Rj_eq_log_floor {n' r : ℕ} (X : Dat n' r) (p K : ℕ) (j : ℤ) :
    X.Rj p K j = Nat.log p ⌊X.a / (8 * X.Y * Dat.k (r := r) K ^ 2 * ↑X.Ns)⌋₊ - X.F.dist j (X.F.fr (j - 1) 0) := by
  unfold Dat.Rj
  rw [div_mul_eq_div_div, ← Nat.cast_pow, Nat.floor_div_natCast]
  exact nat_log_div_pow_eq_sub p _ _

private theorem Pz_eq_Pz_mul_Qc {n' r : ℕ} (X : Dat n' r) (p K : ℕ) (j c x x' s : ℤ)
    (h1 : X.F.fr c (r - 1) = X.F.fr (j - 1) (r - 1) + s)
    (h2 : X.F.fr (c - 1) 0 = X.F.fr (j - 1 - 1) 0 + s)
    (h3 : X.F.fr (c + 1) (r - 1) = X.F.fr j (r - 1) + s)
    (h4 : X.F.fr (c + 1 - 1) 0 = X.F.fr (j - 1) 0 + s)
    (hx' : x' = x + s) (hxT : x ≤ X.F.fr (j - 1) (r - 1))
    (hTT : X.F.fr (j - 1) (r - 1) < X.F.fr j (r - 1))
    (hA : X.F.fr (j - 1) 0 ≤ X.F.fr j (r - 1))
    (hB : X.F.fr (j - 1 - 1) 0 ≤ X.F.fr (j - 1) (r - 1))
    (hC : X.F.fr (j - 1 - 1) 0 < X.F.fr (j - 1) 0) :
    X.Pz p K j x = X.Pz p K c x' * X.Qc p K c := by
  have hRj := Rj_eq_log_floor X p K j
  have hRc := Rj_eq_log_floor X p K c
  have hRc1 := Rj_eq_log_floor X p K (c + 1)
  unfold Dat.Pz Dat.Qc
  rw [hRj, hRc, hRc1, ← pow_add]
  congr 1
  unfold Frames.dist
  omega

theorem restLamGeo (C₀ : ℝ) : RestLamGeo C₀ := by
  classical
  intro p n' r K _ _ _ X hH _ _
  have hV := hH.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hJ : 1 ≤ X.F.J := hV.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j j' x hx x' hx' hp
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hx
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hx'
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 _ _ x x' (by omega) (by omega) (by omega) (by omega)
      a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)
    exact ⟨Fin.ext (by omega), e2⟩
  · intro j j' x hx hW x' hx' hW' hp
    obtain ⟨hl, -⟩ := lam_W_late X hV _ x hx hW
    obtain ⟨hl', -⟩ := lam_W_late X hV _ x' hx' hW'
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hl
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hl'
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV (-1) _ _ x x' (by omega) (by omega) (by omega) (by omega)
      a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)
    exact ⟨Fin.ext (by omega), e2⟩
  · intro j j' x hx hW x' hx' hp
    obtain ⟨hl, i, hi, hxi⟩ := lam_W_late X hV _ x hx hW
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hl
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hx'
    have hj := j.isLt
    have hj' := j'.isLt
    have hTT : X.F.fr (((j : ℕ) : ℤ) - 1) (r - 1) < X.F.fr ((j : ℕ) : ℤ) (r - 1) := by
      have h := fr_last_lt_fr_last_succ X.F hV (((j : ℕ) : ℤ) - 1)
      rwa [sub_add_cancel] at h
    have hf1 := fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
    have hf2 := fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1 - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
    have hg := hV.2.2.2.1 (((j : ℕ) : ℤ) - 1 - 1)
    rw [sub_add_cancel] at hg
    have hA : X.F.fr (((j : ℕ) : ℤ) - 1) 0 ≤ X.F.fr ((j : ℕ) : ℤ) (r - 1) := by omega
    have hC : X.F.fr (((j : ℕ) : ℤ) - 1 - 1) 0 < X.F.fr (((j : ℕ) : ℤ) - 1) 0 := by omega
    have hB : X.F.fr (((j : ℕ) : ℤ) - 1 - 1) 0 ≤ X.F.fr (((j : ℕ) : ℤ) - 1) (r - 1) := by omega
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj0
    · have q1 : X.F.fr (((j : ℕ) : ℤ) - 1 + X.F.J - 1) (r - 1)
          = X.F.fr (((j : ℕ) : ℤ) - 1 - 1) (r - 1) + n' := by
        rw [show ((j : ℕ) : ℤ) - 1 + X.F.J - 1 = ((j : ℕ) : ℤ) - 1 - 1 + X.F.J by ring]
        exact hV.2.1 _ _
      have q2 := hV.2.1 (((j : ℕ) : ℤ) - 1) (r - 1)
      have hpy : (x + n') % (n' : ℤ) = x' % (n' : ℤ) := by
        rw [Int.add_emod_right]
        exact emod_eq_of_posOf_eq' hp
      obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 (((j : ℕ) : ℤ) - 1 + X.F.J) ((j' : ℕ) : ℤ) (x + n') x'
        (by omega) (by omega) (by omega) (by omega) (by rw [q1]; omega) (by rw [q2]; omega) b1 b2 hpy
      refine ⟨⟨i, hi, ?_⟩, ?_⟩
      · rw [← e1, ← e2, hxi]
        exact (hV.2.1 _ _).symm
      · rw [← e1, ← e2]
        refine Pz_eq_Pz_mul_Qc X p K _ _ x _ n' (hV.2.1 _ _) ?_ ?_ ?_ rfl a2 hTT hA hB hC
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J - 1 = ((j : ℕ) : ℤ) - 1 - 1 + X.F.J by ring]
          exact hV.2.1 _ _
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J + 1 = ((j : ℕ) : ℤ) + X.F.J by ring]
          exact hV.2.1 _ _
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J + 1 - 1 = ((j : ℕ) : ℤ) - 1 + X.F.J by ring]
          exact hV.2.1 _ _
    · obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 (((j : ℕ) : ℤ) - 1) ((j' : ℕ) : ℤ) x x'
        (by omega) (by omega) (by omega) (by omega) a1 a2 b1 b2 (emod_eq_of_posOf_eq' hp)
      refine ⟨⟨i, hi, ?_⟩, ?_⟩
      · rw [← e1, ← e2]
        exact hxi
      · rw [← e1, ← e2]
        refine Pz_eq_Pz_mul_Qc X p K _ (((j : ℕ) : ℤ) - 1) x x 0 (by rw [add_zero]) (by rw [add_zero])
          ?_ ?_ (by rw [add_zero]) a2 hTT hA hB hC
        · rw [sub_add_cancel, add_zero]
        · rw [sub_add_cancel, add_zero]
  · intro t ht
    have hper := hV.2.1 (-1) (r - 1)
    obtain ⟨y, hy⟩ : ∃ y : ℤ, y = X.F.fr (-1) (r - 1) + 1
        + (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) % (n' : ℤ) := ⟨_, rfl⟩
    have hy0 := Int.emod_nonneg (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) (ne_of_gt hn)
    have hy1 := Int.emod_lt_of_pos (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) hn
    have ht' := t.isLt
    have hypos : posOf n' y = t := by
      have hmod : y % (n' : ℤ) = ((t : ℕ) : ℤ) := by
        have hy2 : y = ((t : ℕ) : ℤ)
            + (n' : ℤ) * (-((((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) / (n' : ℤ))) := by
          rw [hy, Int.emod_def]
          ring
        rw [hy2, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      unfold posOf
      apply Fin.ext
      simp only
      rw [hmod, Int.toNat_natCast]
      exact Nat.mod_eq_of_lt ht'
    have hyB : y ≤ X.F.fr (((X.F.J - 1 : ℕ)) : ℤ) (r - 1) := by
      rw [show (((X.F.J - 1 : ℕ)) : ℤ) = -1 + X.F.J by omega, hper]
      omega
    have hex : ∃ k : ℕ, y ≤ X.F.fr (k : ℤ) (r - 1) := ⟨_, hyB⟩
    have hk0 := Nat.find_spec hex
    have hk0le := Nat.find_min' hex hyB
    have hmin : ∀ m < Nat.find hex, ¬ y ≤ X.F.fr (m : ℤ) (r - 1) := fun m hm => Nat.find_min hex hm
    generalize Nat.find hex = k0 at hk0 hk0le hmin
    have hlow : X.F.fr ((k0 : ℤ) - 1) (r - 1) < y := by
      rcases Nat.eq_zero_or_pos k0 with h0 | h0
      · subst h0
        rw [Nat.cast_zero, zero_sub]
        omega
      · have h := hmin (k0 - 1) (by omega)
        rw [show (((k0 - 1 : ℕ)) : ℤ) = (k0 : ℤ) - 1 by omega] at h
        omega
    refine ⟨⟨k0, by omega⟩, y, ?_, hypos⟩
    exact mem_late_of_mem_Ioc_of_posOf_mem X hV _ y hlow hk0 (by rw [hypos]; exact ht)

theorem restLamTau : RestLamTau := by
  classical
  intro p n' r K _ _ _ X hH la e j i
  have hV := hH.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hi := i.isLt
  have hj := j.isLt
  have hle : X.F.fr ((j : ℕ) : ℤ) i ≤ X.F.fr ((j : ℕ) : ℤ) (r - 1) :=
    fr_le_fr_of_index_le X.F hV _ (r - 1) (by omega) i (by omega)
  have h0i : X.F.fr ((j : ℕ) : ℤ) 0 ≤ X.F.fr ((j : ℕ) : ℤ) i :=
    fr_le_fr_of_index_le X.F hV _ i hi 0 (Nat.zero_le _)
  have hg := hV.2.2.2.1 (((j : ℕ) : ℤ) - 1)
  rw [sub_add_cancel] at hg
  have h00 := fr_le_fr_of_index_le X.F hV (((j : ℕ) : ℤ) - 1) (r - 1) (by omega) 0 (Nat.zero_le _)
  have hT := (hV.2.2.2.2.1 ((j : ℕ) : ℤ) i hi).1
  have hmem : X.F.fr ((j : ℕ) : ℤ) i ∈ X.F.letters ((j : ℕ) : ℤ) := by
    unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hle⟩, hT⟩
  have hnW : ¬ X.F.IsW ((j : ℕ) : ℤ) (X.F.fr ((j : ℕ) : ℤ) i) := by
    unfold Frames.IsW
    omega
  unfold Dat.bfam
  rw [if_pos hmem, if_neg hnW, if_pos h0i]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    unfold Dat.eZ
    rw [dif_pos (by omega)]
    congr 1
    ext
    have hm : ((j : ℕ) : ℤ) % (X.F.J : ℤ) = ((j : ℕ) : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
    simp only [hm, Int.toNat_natCast]
    exact Nat.mod_eq_of_lt hj
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    have hbl := b.isLt
    rcases lt_trichotomy (b : ℕ) (i : ℕ) with hlt | heq | hgt
    · have h1 := hV.2.2.1 ((j : ℕ) : ℤ) b (by omega)
      have h2 := fr_le_fr_of_index_le X.F hV ((j : ℕ) : ℤ) i hi ((b : ℕ) + 1) (by omega)
      omega
    · exact Fin.ext heq
    · have h1 := hV.2.2.1 ((j : ℕ) : ℤ) i (by omega)
      have h2 := fr_le_fr_of_index_le X.F hV ((j : ℕ) : ℤ) b hbl ((i : ℕ) + 1) (by omega)
      omega
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem restLamInj (C₀ : ℝ) : RestLamInj C₀ := restLamInj_of C₀ (restLamGeo C₀) restLamTau

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

section
namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem restLam_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) (hDeg : RestLamDeg C₀) : RestLam C₀ :=
  restLam_of_rests C₀ (restLamA_of D hAdm) (restLamInj C₀) hDeg

end Formalism.MainNotions.SelectionLemmas.Pf
end
