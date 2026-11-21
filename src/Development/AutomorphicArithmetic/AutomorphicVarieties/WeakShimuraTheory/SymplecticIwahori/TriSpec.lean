import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GramCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.spIwa :
    ∀ {F : Type} [Field F] (V : ValuationSubring F) (h : M4 F), IsGSp 1 h → ∃ k : M4 V, IsGSp 1 k ∧ IsUp (adj (k.map V.subtype) * h) := by
  intro F _ V h hh
  let f : V →+* F := V.subtype
  let hU : GL (Fin 4) F := ⟨h, adj h, mul_adj_self hh, adj_mul_self hh⟩
  obtain ⟨k0, b, hb, hk⟩ := GlobalTheory.ValIwasawa.iwasawa V F 4 hU
  have hbU : IsUp (b : M4 F) := (isUp_iff _).mpr hb
  have hbi : IsUp ((b⁻¹ : GL (Fin 4) F) : M4 F) := IsUp_inv hbU
  have hKmap : (k0 : M4 V).map f = h * ((b⁻¹ : GL (Fin 4) F) : M4 F) := by
    have h1 : (hU : M4 F) =
        ((Matrix.GeneralLinearGroup.map (algebraMap V F) k0 : GL (Fin 4) F) : M4 F) * (b : M4 F) := by
      rw [hk]
      rfl
    have h2 : (hU : M4 F) = h := rfl
    rw [h2] at h1
    rw [h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rfl
  have hadjh : adj (h * ((b⁻¹ : GL (Fin 4) F) : M4 F)) * h = adj ((b⁻¹ : GL (Fin 4) F) : M4 F) := by
    rw [(grp F).1, Matrix.mul_assoc, adj_mul_self hh, Matrix.mul_one]
  have hmapadj : ∀ X : M4 V, adj (X.map f) = (adj X).map f := fun X => (grp V).2.2.2.2.2.1 F f X
  have upMap : ∀ X : M4 V, IsUp (X.map f) → IsUp X := by
    intro X hX i j hij
    have hz := hX i j hij
    simpa [f] using hz
  have hQ : IsUp (adj (k0 : M4 V) * (k0 : M4 V)) := by
    apply upMap
    rw [Matrix.map_mul, ← hmapadj, hKmap, (grp F).1, Matrix.mul_assoc,
      ← Matrix.mul_assoc (adj h), adj_mul_self hh, Matrix.one_mul]
    exact IsUp_mul (IsUp_adj hbi) hbi
  obtain ⟨t, ht, hkt⟩ := gram k0 hQ
  refine ⟨(k0 : M4 V) * (t : M4 V), hkt, ?_⟩
  have htU : IsUp ((t : M4 V).map f) := by
    intro i j hij
    simp [ht i j hij]
  rw [Matrix.map_mul, (grp F).1, hKmap, Matrix.mul_assoc, hadjh]
  exact IsUp_mul (IsUp_adj htU) (IsUp_adj hbi)
end

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

private theorem adj_mul {R : Type} [CommRing R] (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private theorem adj_adj {R : Type} [CommRing R] (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

theorem UpperTheory.V.Ws.Pp.triIwa :
    ∀ {ι A F : Type} [CommRing A] [Field F] (V : ValuationSubring F) (M : ι → M4 A) (P : ι → Fin 4 → A[X]) (g : A →+* V) (h : M4 F), SpTri M P (V.subtype.comp g) h → ∃ k : M4 V, SpTri M P g k := by
  intro ι A F _ _ V M P g h hh
  obtain ⟨k, hk, hb⟩ := spIwa V h hh.1
  refine ⟨k, SpTri.of_map V.subtype Subtype.val_injective ?_⟩
  have a : adj (k.map V.subtype) = (adj k).map V.subtype := by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  have k1 : adj (k.map V.subtype) * k.map V.subtype = 1 := by
    rw [a, ← Matrix.map_mul, adj_mul_self hk, Matrix.map_one _ (map_zero _) (map_one _)]
  generalize k.map V.subtype = K at hb k1
  have h2 : h * adj h = 1 := mul_adj_self hh.1
  have hb' : IsUp (adj h * K) := by
    have := IsUp_adj hb
    rwa [adj_mul, adj_adj] at this
  have one : adj K * h * (adj h * K) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc h, h2, Matrix.one_mul, k1]
  refine ⟨k1.trans (one_smul _ _).symm, fun i => ?_⟩
  have e : ∀ X : M4 F, adj K * X * K = adj K * h * (adj h * X * h) * (adj h * K) := fun X => by
    calc adj K * X * K = adj K * (h * adj h) * X * (h * adj h) * K := by
          rw [h2, Matrix.mul_one, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have c := upConj one hb hb' (hh.2 i).1
  rw [e]
  exact ⟨c.1, fun j => by rw [c.2 j]; exact (hh.2 i).2 j⟩
end

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

open TensorProduct in
theorem UpperTheory.V.Ws.Pp.extFg :
    ∀ {B C K : Type} [CommRing B] [CommRing C] [Field K] [IsAlgClosed K] [Algebra B C] [Algebra.FiniteType B C] (q : Ideal C) [q.IsPrime] (f : B →+* K), RingHom.ker f = q.comap (algebraMap B C) → ∃ φ : C →+* K, φ.comp (algebraMap B C) = f := by
  intro B C K _ _ _ _ _ _ q _ f hf
  letI : Algebra B K := f.toAlgebra
  let p : Ideal B := q.comap (algebraMap B C)
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ {L : Type} [Field L] (g : B →+* L), RingHom.ker g = p →
      ∃ g' : p.ResidueField →+* L, g'.comp (algebraMap B p.ResidueField) = g := by
    intro L _ g hg
    have h2 : p.primeCompl ≤ Submonoid.comap g (IsUnit.submonoid L) := by
      intro x hx
      have : g x ≠ 0 := fun h => hx (by rw [← hg]; exact h)
      exact (isUnit_iff_ne_zero.2 this)
    exact ⟨Ideal.ResidueField.lift p g hg.ge h2,
      RingHom.ext fun x => Ideal.ResidueField.lift_algebraMap p g hg.ge h2 x⟩
  obtain ⟨a, ha⟩ := hunit f hf
  obtain ⟨b, hb⟩ := hunit ((algebraMap C q.ResidueField).comp (algebraMap B C)) (by
    rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField])
  haveI hnt : Nontrivial (K ⊗[B] C) := by
    letI : Algebra p.ResidueField K := a.toAlgebra
    letI : Algebra p.ResidueField q.ResidueField := b.toAlgebra
    haveI : IsScalarTower B p.ResidueField K := IsScalarTower.of_algebraMap_eq' ha.symm
    let T := K ⊗[p.ResidueField] q.ResidueField
    haveI : Nontrivial T := inferInstance
    let u : K →ₐ[B] T := (Algebra.TensorProduct.includeLeft : K →ₐ[B] T)
    let v : C →ₐ[B] T :=
      { toRingHom := ((Algebra.TensorProduct.includeRight : q.ResidueField →ₐ[p.ResidueField] T) : q.ResidueField →+* T).comp (algebraMap C q.ResidueField)
        commutes' := fun x => by
          have h1 : algebraMap C q.ResidueField (algebraMap B C x) =
              algebraMap p.ResidueField q.ResidueField (algebraMap B p.ResidueField x) :=
            (RingHom.congr_fun hb x).symm
          show (Algebra.TensorProduct.includeRight : q.ResidueField →ₐ[p.ResidueField] T) (algebraMap C q.ResidueField (algebraMap B C x)) = _
          rw [h1, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
    exact (Algebra.TensorProduct.lift u v (fun _ _ => Commute.all _ _)).toRingHom.domain_nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[B] C)
  letI : Field ((K ⊗[B] C) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K ((K ⊗[B] C) ⧸ m) := finite_of_finite_type_of_isJacobsonRing _ _
  have hbij : Function.Bijective (algebraMap K ((K ⊗[B] C) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : ((K ⊗[B] C) ⧸ m) →ₐ[K] K := (AlgEquiv.ofBijective (Algebra.ofId K _) hbij).symm.toAlgHom
  let χ : (K ⊗[B] C) →ₐ[K] K := ψ.comp (Ideal.Quotient.mkₐ K m)
  refine ⟨(χ : K ⊗[B] C →+* K).comp ((Algebra.TensorProduct.includeRight : C →ₐ[B] K ⊗[B] C) : C →+* K ⊗[B] C), ?_⟩
  ext x
  show χ ((Algebra.TensorProduct.includeRight : C →ₐ[B] K ⊗[B] C) (algebraMap B C x)) = f x
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B K (K ⊗[B] C), AlgHom.commutes]
  rfl
end

section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

theorem UpperTheory.V.Ws.Pp.triSpec :
    ∀ {ι A F K : Type} [CommRing A] [Field F] [Field K] [IsAlgClosed K] (M : ι → M4 A) (P : ι → Fin 4 → A[X]) (φ : A →+* F) (f : A →+* K) (h : M4 F), RingHom.ker φ ≤ RingHom.ker f → SpTri M P φ h → ∃ h' : M4 K, SpTri M P f h' := by
  intro ι A F K _ _ _ _ M P φ f h hf H
  classical
  haveI := RingHom.ker_isPrime f
  have hu : ∀ y : (RingHom.ker f).primeCompl, IsUnit (φ y) := fun y => Ne.isUnit fun e => y.2 (hf e)
  obtain ⟨V, hV, hl⟩ := IsLocalRing.exists_factor_valuationRing
    (IsLocalization.lift (S := Localization.AtPrime (RingHom.ker f)) hu)
  let g₀ : Localization.AtPrime (RingHom.ker f) →+* V := (IsLocalization.lift hu).codRestrict V.toSubring hV
  haveI : IsLocalHom g₀ := hl
  let g : A →+* V := g₀.comp (algebraMap _ _)
  have hg : V.subtype.comp g = φ := RingHom.ext fun a => IsLocalization.lift_eq hu a
  have hk : RingHom.ker f = (maximalIdeal V).comap g := by
    ext a
    rw [Ideal.mem_comap,
      ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime (RingHom.ker f)) (RingHom.ker f) a,
      mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact (isUnit_map_iff g₀ _).not.symm
  obtain ⟨k, hk'⟩ := triIwa V M P g h (by rw [hg]; exact H)
  letI : Algebra A V := g.toAlgebra
  let s : Set V := Set.range (fun p : Fin 4 × Fin 4 => k p.1 p.2)
  have hs : s.Finite := Set.finite_range _
  let C := Algebra.adjoin A s
  haveI : Algebra.FiniteType A C := (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  let Y : M4 C := fun a b => ⟨k a b, Algebra.subset_adjoin ⟨(a, b), rfl⟩⟩
  have H0 : SpTri M P (algebraMap A C) Y := SpTri.of_map C.val.toRingHom Subtype.val_injective hk'
  let q : Ideal C := (maximalIdeal V).comap C.val.toRingHom
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨ψ, hψ⟩ := extFg q f (by rw [hk]; rfl)
  exact ⟨Y.map ψ, hψ ▸ H0.map ψ⟩
end
