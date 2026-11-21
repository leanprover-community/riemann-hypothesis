import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.PhiSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.AcConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.SelSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.maxIndep :
    ∀ {A M : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [AddCommGroup M] [Module A M] (t : A) (S B : Submodule A M), Irreducible t → S.FG → ∃ (g : ℕ) (κ : Fin g → M), (∀ j, κ j ∈ S) ∧ (∀ c : Fin g → A, ∑ j, c j • κ j ∈ B → c = 0) ∧ ∀ z ∈ S, ∃ (s : ℕ) (c : Fin g → A), t ^ s • z - ∑ j, c j • κ j ∈ B := by
  intro A M _ _ _ _ _ t S B ht hS
  haveI : Module.Finite A (S.map B.mkQ) := Module.Finite.iff_fg.mpr (hS.map _)
  obtain ⟨n, ι, _, p, hp, e, ⟨φ⟩⟩ := Module.equiv_free_prod_directSum A (S.map B.mkQ)
  let ψ : (Fin n →₀ A) →ₗ[A] S.map B.mkQ := φ.symm.toLinearMap ∘ₗ LinearMap.inl A _ _
  have hlift : ∀ j : Fin n, ∃ m ∈ S, B.mkQ m = (ψ (Finsupp.single j 1) : M ⧸ B) :=
    fun j => Submodule.mem_map.mp (ψ (Finsupp.single j 1)).2
  choose κ hκS hκ using hlift
  have hψinj : Function.Injective ψ := φ.symm.injective.comp LinearMap.inl_injective
  have hli : LinearIndependent A (fun j => (ψ (Finsupp.single j 1) : M ⧸ B)) := by
    have h1 := (Finsupp.basisSingleOne (R := A) (ι := Fin n)).linearIndependent
    have h2 := h1.map' ψ (LinearMap.ker_eq_bot.mpr hψinj)
    have h3 := h2.map' (S.map B.mkQ).subtype (Submodule.ker_subtype _)
    simpa [Function.comp_def] using h3
  refine ⟨n, κ, hκS, ?_, ?_⟩
  · intro c hc
    have h0 : ∑ j, c j • (ψ (Finsupp.single j 1) : M ⧸ B) = 0 := by
      simp_rw [← hκ, ← map_smul, ← map_sum]
      exact (Submodule.Quotient.mk_eq_zero B).mpr hc
    funext j
    exact Fintype.linearIndependent_iff.mp hli c h0 j
  · intro z hz
    let w : S.map B.mkQ := ⟨B.mkQ z, Submodule.mem_map_of_mem hz⟩
    let K := ∑ i, e i
    have hd : t ^ K • (φ w).2 = 0 := by
      refine DFinsupp.ext fun i => ?_
      rw [DirectSum.smul_apply, DirectSum.zero_apply]
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ ((φ w).2 i)
      rw [← hx, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_span_singleton]
      obtain ⟨u, hu⟩ := ((IsDiscreteValuationRing.associated_of_irreducible A (hp i) ht).pow_pow (n := e i)).dvd.trans
        (pow_dvd_pow t (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))
      exact ⟨u * x, by rw [hu, smul_eq_mul, smul_eq_mul]; ring⟩
    have hφ : t ^ K • w = ψ (t ^ K • (φ w).1) := by
      apply φ.injective
      rw [map_smul]
      show t ^ K • φ w = φ (φ.symm (t ^ K • (φ w).1, 0))
      rw [LinearEquiv.apply_symm_apply]
      ext1
      · rfl
      · exact hd
    refine ⟨K, fun j => t ^ K * (φ w).1 j, ?_⟩
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_smul, map_sum]
    simp_rw [map_smul, hκ]
    have hz' : B.mkQ z = (w : M ⧸ B) := rfl
    rw [hz', sub_eq_zero, ← Submodule.coe_smul, hφ]
    conv_lhs => rw [← Finsupp.univ_sum_single (t ^ K • (φ w).1)]
    rw [map_sum, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.smul_apply, smul_eq_mul, ← Finsupp.smul_single_one, map_smul, Submodule.coe_smul]
end

section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charP_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have hpl : p = l := by
    by_contra hne
    have hcop : l.Coprime p := (Nat.coprime_primes (Fact.out) hpp).2 (Ne.symm hne)
    have hu : IsUnit ((p : ℕ) : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hcop)
    have hu' := hu.map f
    rw [map_natCast, hpK] at hu'
    exact not_isUnit_zero hu'
  subst hpl
  exact hp

theorem UpperTheory.V.Pa.Det.kapEx :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), PhiCond F.Γ l → Nonempty (Kap x) := by
  intro l _ F n x hΦ
  letI : Field x.K := x.field
  haveI : Finite x.K := x.fin
  letI : Algebra ℤ_[l] x.K := x.algZ
  haveI : CharP x.K l := charP_of_padic (algebraMap ℤ_[l] x.K)
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  have hΦ0 : PhiCond F.G₀ l := UpperTheory.V.Pa.Det.phiSub l F.η.ker F.η_open hΦ
  have hρ : x.ρX x.A = fun g => mat x.ρ g := by
    funext g
    simp [UpperTheory.V.Pa.NP.ρX, Algebra.algebraMap_self]
  obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := UpperTheory.V.Pa.Det.selSub F (A := x.A) (R := x.A) x.t (x.ρX x.A)
    (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)
  have hSfg : S.FG := by
    refine UpperTheory.V.Pa.Det.matFg l (K := x.K) (G := F.G₀) (R := x.A) (1 : F.G₀ →* x.A) (mat x.ρ) S hΦ0
      ?_ ?_ ?_
    · intro N
      simp only [MonoidHom.one_apply]
      exact IsLocallyConstant.const (X := F.G₀) _
    · intro i j
      have h := x.cont i j
      simpa [PowerSeries.maximalIdeal_eq_span_X] using h
    · intro z hz
      rw [← SetLike.mem_coe, hS] at hz
      refine ⟨hz.2.1, ?_⟩
      intro g _ h _
      have e := hz.2.2.1 g h
      rw [hρ] at e
      simpa using e
  obtain ⟨g, κ, hmem, hind, hgen⟩ :=
    UpperTheory.V.Pa.Det.maxIndep x.t S B PowerSeries.X_irreducible hSfg
  have hsel : ∀ j, κ j ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    intro j
    rw [← hS]
    exact hmem j
  have hloc : ∀ j v, ∃ Y ∈ Od x.A x.A n x.a,
      LocAt F (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (κ j) v Y :=
    fun j v => (hsel j).2.2.2.2.2 v
  choose Y hYmem hYloc using hloc
  refine ⟨⟨g, κ, hsel, Y, hYmem, hYloc, ?_, ?_⟩⟩
  · intro c hc
    apply hind c
    rw [← SetLike.mem_coe, hB]
    exact hc
  · intro z hz
    rw [← hS] at hz
    obtain ⟨s, c, hsc⟩ := hgen z hz
    refine ⟨s, c, ?_⟩
    rw [← hB]
    exact hsc
end
