import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]

private theorem adj_up {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := fun i j h => by
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

private theorem adj_diag {R : Type} [CommRing R] (X : M4 R) (i : Fin 4) : adj X i i = X i.rev i.rev := by
  have h : sgn i * sgn i = 1 := by revert i; decide
  rw [adj_apply, h, one_smul]

private theorem gsp_diag {R : Type} [CommRing R] {ν : R} {n X : M4 R} (hn : IsGSp 1 n) (hX : IsGSp ν X)
    (hu : IsUp (adj n * X * n)) (i : Fin 4) : (adj n * X * n) i.rev i.rev * (adj n * X * n) i i = ν := by
  obtain ⟨hmul, hadj, -⟩ := grp R
  have h1 : adj n * n = 1 := by simpa [IsGSp] using hn
  have h2 : n * adj n = 1 := mul_eq_one_comm.1 h1
  have h3 : adj (adj n * X * n) * (adj n * X * n) = ν • (1 : M4 R) := by
    have hX' : adj X * X = ν • (1 : M4 R) := hX
    rw [hmul, hmul, hadj]
    calc adj n * (adj X * n) * (adj n * X * n) = adj n * (adj X * (n * adj n) * X) * n := by simp only [mul_assoc]
      _ = ν • (1 : M4 R) := by rw [h2, mul_one, hX', mul_smul_comm, mul_one, smul_mul_assoc, h1]
  have h4 := up_mul_diag (adj_up hu) hu i
  rw [adj_diag, h3] at h4
  simpa using h4.symm

private theorem closure_comm {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CommRing R]
    (I : Ideal R) [IsHausdorff I R] (H : Subgroup Γ) (f : Γ → R) (h1 : f 1 = 1)
    (hm : ∀ s ∈ H, ∀ t ∈ H, f (s * t) = f s * f t) (hc : AdicCont I f) :
    ∀ c ∈ (⁅H, H⁆ : Subgroup Γ).topologicalClosure, f c = 1 := by
  have hi : ∀ s ∈ H, f s * f s⁻¹ = 1 := fun s hs => by rw [← hm s hs _ (H.inv_mem hs), mul_inv_cancel, h1]
  let K : Subgroup Γ :=
    { carrier := {g | g ∈ H ∧ f g = 1}
      one_mem' := ⟨H.one_mem, h1⟩
      mul_mem' := fun {s t} hs ht => ⟨H.mul_mem hs.1 ht.1, by rw [hm s hs.1 t ht.1, hs.2, ht.2, mul_one]⟩
      inv_mem' := fun {s} hs => ⟨H.inv_mem hs.1, by have := hi s hs.1; rwa [hs.2, one_mul] at this⟩ }
  have hK : ⁅H, H⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro s hs t ht
    have a1 := H.mul_mem hs ht
    have a2 := H.mul_mem a1 (H.inv_mem hs)
    rw [commutatorElement_def]
    refine ⟨H.mul_mem a2 (H.inv_mem ht), ?_⟩
    rw [hm _ a2 _ (H.inv_mem ht), hm _ a1 _ (H.inv_mem hs), hm _ hs _ ht]
    linear_combination (f t * f t⁻¹) * hi s hs + hi t ht
  intro c hcm
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) inferInstance _ fun N => ?_
  have hcl := (hc N).isClosed_fiber (Ideal.Quotient.mk (I ^ N) 1)
  have : c ∈ {g | Ideal.Quotient.mk (I ^ N) (f g) = Ideal.Quotient.mk (I ^ N) 1} :=
    closure_minimal (fun g hg => by
      show Ideal.Quotient.mk (I ^ N) (f g) = _
      rw [(hK hg).2]) hcl hcm
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq.1 this

private theorem conj_cont {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (r : Γ → M4 R)
    (h : ∀ i j, AdicCont I fun g => r g i j) (A B : M4 R) (i j : Fin 4) : AdicCont I fun g => (A * r g * B) i j := by
  intro N
  have h0 : IsLocallyConstant fun g => (r g).map (Ideal.Quotient.mk (I ^ N)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have := fun p : Fin 4 × Fin 4 => (h p.1 p.2 N).eventually_eq x
    filter_upwards [Filter.eventually_all.2 this] with y hy
    ext a b
    exact hy (a, b)
  have h2 := h0.comp fun X => (A.map (Ideal.Quotient.mk (I ^ N)) * X * B.map (Ideal.Quotient.mk (I ^ N))) i j
  convert h2 using 2 with g
  simp only [Function.comp_apply, ← Matrix.map_mul, Matrix.map_apply]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.muIff :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ ζ : Φ.ι → Γ, (∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v)) → (∀ v, a (Φ.ν (ζ v)) = 1) → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.noMu.Lifts a c P → (Φ.Lifts a c P ↔ ∀ v, P.ψ v 0 (ζ v) = 1 ∧ P.ψ v 1 (ζ v) = 1) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS c _ ζ hζ hν R _ _ _ P hP
  refine ⟨fun h v => ⟨h.pair.mu v _ (hζ v).1 0, h.pair.mu v _ (hζ v).1 1⟩, fun h => ?_⟩
  obtain ⟨⟨hmult, hkill, hnrm, hlow, hflag, -⟩, hcont, hred⟩ := hP
  refine ⟨⟨hmult, hkill, hnrm, hlow, hflag, fun v s hs i => ?_⟩, hcont, hred⟩
  have hn : IsGSp 1 (P.n v) := (hlow v).1
  have n1 : adj (P.n v) * P.n v = 1 := by simpa [IsGSp] using hn
  have n2 : P.n v * adj (P.n v) = 1 := mul_eq_one_comm.1 n1
  have hz : ζ v ∈ Φ.Gv v := (hS.mu v _ (hζ v).1).1
  have hsG : s ∈ Φ.Gv v := (hS.mu v _ hs).1
  have hrev : ∀ j : Fin 4, P.ψ v j.rev (ζ v) * P.ψ v j (ζ v) = 1 := fun j => by
    have := gsp_diag hn (hmult (ζ v)) (hflag v _ hz) j
    rw [RingHom.comp_apply] at this
    erw [hν v] at this
    rwa [map_one] at this
  have hzi : P.ψ v i (ζ v) = 1 := by
    have e0 := hrev 0
    have e1 := hrev 1
    rw [(h v).1, mul_one] at e0
    rw [(h v).2, mul_one] at e1
    fin_cases i
    exacts [(h v).1, (h v).2, e1, e0]
  have h1 : P.ψ v i 1 = 1 := by simp [PD.ψ, n1]
  have hm : ∀ s ∈ Φ.Gv v, ∀ t ∈ Φ.Gv v, P.ψ v i (s * t) = P.ψ v i s * P.ψ v i t := fun s hs t ht => by
    unfold PD.ψ
    rw [← up_mul_diag (hflag v s hs) (hflag v t ht), map_mul]
    refine congrFun (congrFun ?_ i) i
    calc adj (P.n v) * (P.r s * P.r t) * P.n v
        = adj (P.n v) * P.r s * (P.n v * adj (P.n v)) * P.r t * P.n v := by rw [n2]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have hpow : ∀ n : ℕ, P.ψ v i (ζ v ^ n) = 1 := fun n => by
    induction n with
    | zero => rw [pow_zero, h1]
    | succ n ih => rw [pow_succ, hm _ (pow_mem hz n) _ hz, ih, hzi, mul_one]
  obtain ⟨n, hn'⟩ := (hζ v).2 s hs
  have hc := closure_comm (maximalIdeal R) (Φ.Gv v) (P.ψ v i) h1 hm
    (conj_cont _ (fun g => P.r g) hcont _ _ i i) _ hn'
  have := hm _ (mul_mem hsG (inv_mem (pow_mem hz n))) _ (pow_mem hz n)
  rwa [inv_mul_cancel_right, hc, hpow, mul_one] at this
end

section
open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at hp
  · exact h.cont.map _ (fun x hx =>
      (res_eq_zero_iff Λ R' _).mp ((res_map f x).trans ((res_eq_zero_iff Λ R x).mpr hx)))
  · rw [PD.map_map]
    convert h.red using 2
    exact RingHom.ext fun x => res_map f x

private theorem lifts_noMu {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) : Φ.noMu.Lifts a c P :=
  ⟨⟨h.pair.mult, h.pair.kill, h.pair.nrm, h.pair.low, h.pair.flag, fun _ _ hs => hs.elim⟩, h.cont, h.red⟩

theorem UpperTheory.V.Ws.X1.muQuot :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → ∀ ζ : Φ.ι → Γ, (∀ v, MuGen (Φ.Gv v) (Φ.Mu v) (ζ v)) → (∀ v, a (Φ.ν (ζ v)) = 1) → ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (P' : PD Φ.ι Γ R'), Φ.noMu.IsDef a c P' → ∃ (g : R' →ₐ[Λ] R) (e : Φ.ι × Fin 2 → R'), Function.Surjective g ∧ RingHom.ker g = Ideal.span (Set.range e) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd c hres ζ hζ hν R _ _ _ P hP R' _ _ _ P' hP'
  obtain ⟨g, hg, -⟩ := hP'.2 R P (lifts_noMu hP.1)
  have hPψ := (X1.muIff Φ l a hstd c hres ζ hζ hν R P (lifts_noMu hP.1)).mp hP.1
  let e : Φ.ι × Fin 2 → R' := fun p => P'.ψ p.1 (Fin.castLE (by norm_num) p.2) (ζ p.1) - 1
  let I : Ideal R' := Ideal.span (Set.range e)
  have hIg : ∀ x ∈ I, g x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨⟨v, i⟩, rfl⟩
      have key : ∀ j : Fin 4, g (P'.ψ v j (ζ v)) = P.ψ v j (ζ v) := by
        intro j
        rw [← hg, PD.map_ψ]
        rfl
      fin_cases i
      · simp [e, key, (hPψ v).1]
      · simp [e, key, (hPψ v).2]
    · exact map_zero g
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_eq_mul, map_mul, hx, mul_zero]
  have hne : I ≠ ⊤ := by
    intro htop
    have h1 := hIg 1 (htop ▸ Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (R' ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  let π : R' →ₐ[Λ] R' ⧸ I := Ideal.Quotient.mkₐ Λ I
  haveI : IsCO Λ (R' ⧸ I) := co_quot Λ R' (R' ⧸ I) π (Ideal.Quotient.mkₐ_surjective Λ I)
  have hQn : Φ.noMu.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := lifts_map hP'.1 π
  have hQ : Φ.Lifts a c (P'.map (π : R' →+* R' ⧸ I)) := by
    refine (X1.muIff Φ l a hstd c hres ζ hζ hν (R' ⧸ I) _ hQn).mpr (fun v => ⟨?_, ?_⟩)
    · rw [PD.map_ψ]
      have hm : e (v, 0) ∈ I := Ideal.subset_span ⟨(v, 0), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
    · rw [PD.map_ψ]
      have hm : e (v, 1) ∈ I := Ideal.subset_span ⟨(v, 1), rfl⟩
      have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr hm
      simp only [e, map_sub, map_one] at hz
      exact sub_eq_zero.mp hz
  obtain ⟨h, hh, -⟩ := hP.2 (R' ⧸ I) _ hQ
  obtain ⟨π', -, huniq⟩ := hP'.2 (R' ⧸ I) _ hQn
  have hhg : h.comp g = π := by
    rw [huniq (h.comp g) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hg, hh]),
      huniq π rfl]
  let gb : R' ⧸ I →ₐ[Λ] R := Ideal.Quotient.liftₐ I g hIg
  obtain ⟨i0, -, huniqP⟩ := hP.2 R P hP.1
  have hgb : gb.comp π = g := by
    ext x
    rfl
  have hid : gb.comp h = AlgHom.id Λ R := by
    rw [huniqP (gb.comp h) (by beta_reduce; rw [AlgHom.comp_toRingHom, ← PD.map_map, hh, PD.map_map,
        ← AlgHom.comp_toRingHom, hgb, hg]),
      huniqP (AlgHom.id Λ R) (by beta_reduce; rw [← hg, PD.map_map]; rfl)]
  refine ⟨g, e, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective Λ I (h y)
    refine ⟨z, ?_⟩
    have hy := congrArg (fun f : R →ₐ[Λ] R => f y) hid
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at hy
    rw [← hz] at hy
    exact hy
  · apply le_antisymm
    · intro x hx
      have hx' : π x = 0 := by
        rw [← hhg, AlgHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem).mp hx'
    · intro x hx
      exact RingHom.mem_ker.mpr (hIg x hx)
end
