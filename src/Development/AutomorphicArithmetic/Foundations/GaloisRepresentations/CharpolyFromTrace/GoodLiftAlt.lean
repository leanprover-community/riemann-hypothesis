import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.UnlinkedOfType
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleOfRestrictNormalFiniteIndex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.ScalarOfCharpoly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrinciple

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

theorem UpperTheory.Gal.NearKilling.killTransfer : KillTransfer := by
  intro I V V' _ _ _ _ _ _ _ ρ ρ' hfin htr x hx
  have h1 : ∀ y : MonoidAlgebra ℂ I,
      LinearMap.trace ℂ V (ρ.asAlgebraHom y) = LinearMap.trace ℂ V' (ρ'.asAlgebraHom y) := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g => simpa [Representation.asAlgebraHom_of] using htr g
    | add a b ha hb => simp only [map_add, ha, hb]
    | smul c a ha => simp only [map_smul, ha]
  have h2 : ∀ g : I, LinearMap.trace ℂ V (ρ.asAlgebraHom x * ρ g) = 0 := by
    intro g
    have h3 : ρ.asAlgebraHom x * ρ g = ρ.asAlgebraHom (x * MonoidAlgebra.of ℂ I g) := by
      rw [map_mul, Representation.asAlgebraHom_of]
    rw [h3, h1, map_mul, hx, zero_mul, map_zero]
  let b := Module.finBasis ℂ V
  let φ := LinearMap.toMatrixAlgEquiv (R := ℂ) b
  let r : I →* GL (Fin (Module.finrank ℂ V)) ℂ := (φ.toAlgHom.toMonoidHom.comp ρ).toHomUnits
  have hr : ∀ g, ((r g : GL (Fin (Module.finrank ℂ V)) ℂ) : Matrix _ _ ℂ) = φ (ρ g) := by
    intro g
    simp [r, MonoidHom.coe_toHomUnits]
  have hrange : Finite r.range := by
    have hsub : (Set.range r).Finite := by
      refine Set.Finite.of_finite_image (f := fun u : GL (Fin (Module.finrank ℂ V)) ℂ => (u : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ)) ?_
        (fun _ _ _ _ h => Units.ext h)
      refine (hfin.image φ).subset ?_
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨ρ g, ⟨g, rfl⟩, (hr g).symm⟩
    exact hsub.to_subtype
  have hss : IsSSRep r := by
    refine GlobalTheory.ssRep_of_normal_finiteIndex _ _ _ r r.ker inferInstance inferInstance ?_
    intro W _
    obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
    refine ⟨W', ?_, hW'⟩
    intro g v hv
    have hg : r (g : I) = 1 := g.2
    simpa [hg] using hv
  have hspan : ∀ y : MonoidAlgebra ℂ I, φ (ρ.asAlgebraHom y) ∈
      Submodule.span ℂ (Set.range fun g => ((r g : GL (Fin (Module.finrank ℂ V)) ℂ) : Matrix _ _ ℂ)) := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      rw [Representation.asAlgebraHom_of, ← hr]
      exact Submodule.subset_span ⟨g, rfl⟩
    | add a c ha hc =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hc
    | smul c a ha =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c ha
  have h0 : φ (ρ.asAlgebraHom x) = 0 := by
    refine GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep ℂ I _ r hss _ (hspan x) ?_
    intro g
    rw [hr, ← map_mul, ← h2 g, LinearMap.trace_eq_matrix_trace ℂ b]
    rfl
  exact φ.injective (by rw [h0, map_zero])
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem charpoly_of_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (c : ℂ) (hf : ∀ v, f v = c • v) :
    f.charpoly = (X - C c) ^ Module.finrank ℂ V := by
  have e : LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f
      = Matrix.diagonal fun _ => c := by
    ext i j
    simp [LinearMap.toMatrix_apply, hf, Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V), e, Matrix.charpoly_diagonal]
  simp

theorem UpperTheory.Gal.NearKilling.splitOff :
    SplitOff := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ z c γ q hq hcj h1 h2 h3
  classical
  set f := z.ρ (ineIncl h γ) with hf
  let U : Submodule ℂ V := Module.End.eigenspace f (c γ)
  let R : Submodule ℂ V := LinearMap.range (f - c γ • (1 : Module.End ℂ V))
  let Q : Submodule ℂ V := LinearMap.ker (aeval f q)
  have hUq : ∀ v ∈ U, aeval f q v = q.eval (c γ) • v := fun v hv => by
    by_cases h0 : v = 0
    · simp [h0]
    · exact Module.End.aeval_apply_of_hasEigenvector ⟨hv, h0⟩
  have hUs : ∀ v ∈ U, ∀ s : ↥(Ine (F := E) A), z.ρ (ineIncl h s) v = c s • v := fun v hv s => by
    have k := LinearMap.congr_fun (h1 s) v
    rw [Module.End.mul_apply, hUq v hv, map_smul] at k
    have k2 := (smul_eq_zero.1 k).resolve_left hq
    simpa [sub_eq_zero] using k2
  have hUQ : ∀ v, v ∈ U → v ∈ Q → v = 0 := fun v hv hv' => by
    have k : aeval f q v = 0 := hv'
    rw [hUq v hv] at k
    exact (smul_eq_zero.1 k).resolve_left hq
  have hRQ : R ≤ Q := by
    rintro _ ⟨u, rfl⟩
    exact LinearMap.congr_fun (h2 γ) u
  have hUR : IsCompl U R := by
    refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 ?_
    · have := LinearMap.finrank_range_add_finrank_ker (f - c γ • (1 : Module.End ℂ V))
      rw [← Module.End.eigenspace_def] at this
      change Module.finrank ℂ R + Module.finrank ℂ U = _ at this
      omega
    · exact Submodule.disjoint_def.2 fun v hv hv' => hUQ v hv (hRQ hv')
  have hQR : Q ≤ R := fun v hv => by
    have : v ∈ U ⊔ R := by rw [hUR.sup_eq_top]; trivial
    obtain ⟨u, hu, r, hr, rfl⟩ := Submodule.mem_sup.1 this
    have hu' : u ∈ Q := by
      have := Q.sub_mem hv (hRQ hr)
      simpa using this
    rw [hUQ u hu hu', zero_add]
    exact hr
  have hc : IsCompl Q U := by
    rw [le_antisymm hQR hRQ]
    exact hUR.symm
  have hU : ∀ σ, ∀ v ∈ U, z.ρ σ v ∈ U := fun g v hv => by
    have e : f (z.ρ g v) = z.ρ g (z.ρ (ineIncl h (ineConj g⁻¹ γ)) v) := by
      rw [hf, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ineIncl_ineConj]
      simp [mul_assoc]
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [e, hUs v hv, hcj, map_smul]
  have hQ : ∀ σ, ∀ v ∈ Q, z.ρ σ v ∈ Q := fun g v hv => by
    obtain ⟨u, rfl⟩ := hQR hv
    have e : z.ρ g ((f - c γ • (1 : Module.End ℂ V)) u)
        = (z.ρ (ineIncl h (ineConj g γ)) - c (ineConj g γ) • (1 : Module.End ℂ V)) (z.ρ g u) := by
      have e1 : z.ρ (ineIncl h (ineConj g γ)) (z.ρ g u) = z.ρ g (f u) := by
        rw [hf, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ineIncl_ineConj]
        simp [mul_assoc]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, e1, hcj]
    show aeval f q _ = 0
    rw [e]
    exact LinearMap.congr_fun (h2 (ineConj g γ)) (z.ρ g u)
  let a := z.resZero Q hQ
  let b := z.resZero U hU
  let e := Submodule.prodEquivOfIsCompl Q U hc
  have hb : ∀ (s : ↥(Ine (F := E) A)) (v : U), b.ρ (ineIncl h s) v = c s • v := fun s v =>
    Subtype.ext (hUs v v.2 s)
  have ha : ∀ v, a.ρ (ineIncl h γ) v = c γ • v → v = 0 := fun v hv => by
    have k : z.ρ (ineIncl h γ) (v : V) = c γ • (v : V) := congrArg Subtype.val hv
    exact Subtype.ext (hUQ v (Module.End.mem_eigenspace_iff.2 k) v.2)
  have hg : ∀ σ v, e.symm (z.ρ σ v) = (a.sum b).ρ σ (e.symm v) := fun σ v => by
    obtain ⟨p, rfl⟩ := e.surjective v
    rw [e.symm_apply_apply, LinearEquiv.symm_apply_eq]
    simp [e, a, b, Submodule.coe_prodEquivOfIsCompl', WDRep.resZero]
  have h0 : ∀ v, z.N (e.symm.symm (0, v)) = 0 := fun v => by
    have k : e.symm.symm (0, v) = (v : V) := by simp [e, Submodule.coe_prodEquivOfIsCompl']
    rw [k]
    exact h3 v (hUs v v.2)
  obtain ⟨a', ea⟩ := UpperTheory.GalN.exists_sum z a b e.symm hg rfl (ineIncl h γ) (deg_ineIncl _) (c γ) (hb γ) ha h0
  have hbc : ∀ s : ↥(Ine (F := E) A), (b.ρ (ineIncl h s)).charpoly = (X - C (c s)) ^ Module.finrank ℂ U :=
    fun s => charpoly_of_scalar _ _ (hb s)
  have hm : f.charpoly.rootMultiplicity (c γ) = Module.finrank ℂ U := by
    have k := z.charpoly_eq_mul_of_isCompl Q U hQ hU hc (ineIncl h γ)
    have hne := (LinearMap.charpoly_monic (a.ρ (ineIncl h γ))).ne_zero
    have hroot : ¬ (a.ρ (ineIncl h γ)).charpoly.IsRoot (c γ) := fun hr => by
      have hev := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hr
      obtain ⟨v, hv, hv0⟩ := hev.exists_hasEigenvector
      exact hv0 (ha v (Module.End.mem_eigenspace_iff.1 hv))
    rw [hf, k]
    show ((a.ρ (ineIncl h γ)).charpoly * (b.ρ (ineIncl h γ)).charpoly).rootMultiplicity (c γ) = _
    rw [hbc γ, rootMultiplicity_mul (mul_ne_zero hne ((monic_X_sub_C _).pow _).ne_zero),
      rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hroot, zero_add]
  rw [hm]
  refine ⟨WD.mk a', WD.mk b, by rw [WD.lpSum_mk]; exact ea, WD.lpDim_mk b, (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 rfl, fun σ hσ => ?_⟩
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk]
  exact hbc ⟨σ, hσ⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem trace_eq_of_charpoly {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {f : Module.End ℂ V} {g : Module.End ℂ V'}
    (e : f.charpoly = g.charpoly) : LinearMap.trace ℂ V f = LinearMap.trace ℂ V' g := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _), e]

private theorem aeval_prodMap' {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (f : Module.End ℂ V) (g : Module.End ℂ V') (q : ℂ[X]) :
    aeval (f.prodMap g : Module.End ℂ (V × V')) q = (aeval f q).prodMap (aeval g q) := by
  have h2 : aeval ((f, g) : Module.End ℂ V × Module.End ℂ V') q = (aeval f q, aeval g q) := by
    induction q using Polynomial.induction_on' with
    | add p r hp hr => simp [hp, hr]
    | monomial n a => simp [aeval_monomial]
  have h := Polynomial.aeval_algHom_apply (LinearMap.prodMapAlgHom ℂ V V') (f, g) q
  rw [h2] at h
  exact h

private theorem kill_mul (kt : KillTransfer) {I V V' : Type} [Group I] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (ρ : Representation ℂ I V) (ρ' : Representation ℂ I V') (hf : (Set.range ρ).Finite)
    (ht : ∀ s, LinearMap.trace ℂ V (ρ s) = LinearMap.trace ℂ V' (ρ' s)) (s γ : I) (a : ℂ) (q : ℂ[X]) :
    ((ρ' s - a • 1) * aeval (ρ' γ) q = 0 → (ρ s - a • 1) * aeval (ρ γ) q = 0) ∧
    (aeval (ρ' γ) q * (ρ' s - a • 1) = 0 → aeval (ρ γ) q * (ρ s - a • 1) = 0) := by
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (r : Representation ℂ I W),
      r.asAlgebraHom (MonoidAlgebra.single s 1 - a • 1) = r s - a • 1 ∧
      r.asAlgebraHom (aeval (MonoidAlgebra.single γ (1 : ℂ)) q) = aeval (r γ) q := by
    intro W _ _ r
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_smul, map_one, Representation.asAlgebraHom_single_one]
    · rw [← Polynomial.aeval_algHom_apply, Representation.asAlgebraHom_single_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := kt I V V' ρ ρ' hf ht ((MonoidAlgebra.single s 1 - a • 1) * aeval (MonoidAlgebra.single γ (1 : ℂ)) q)
      (by rw [map_mul, (key ρ').1, (key ρ').2]; exact h)
    rwa [map_mul, (key ρ).1, (key ρ).2] at this
  · have := kt I V V' ρ ρ' hf ht (aeval (MonoidAlgebra.single γ (1 : ℂ)) q * (MonoidAlgebra.single s 1 - a • 1))
      (by rw [map_mul, (key ρ').1, (key ρ').2]; exact h)
    rwa [map_mul, (key ρ).1, (key ρ).2] at this

structure UpperTheory.Gal.NearKilling.IneRelInv {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (x y : WD h) : Prop where
  pol : ∀ s, x.charPol (ineIncl h s) = y.charPol (ineIncl h s)
  eig : ∀ ξ : ↥(Ine (F := E) A) → ℂ, (∀ (g : Weil h) s, ξ (ineConj g s) = ξ s) → EigZero y ξ → EigZero x ξ

theorem UpperTheory.Gal.NearKilling.IneRelInv.spl {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h} (hr : IneRelInv x y)
    (u : WD h) (c : G E Ω → ℂ) (t : ℕ) (γ : G E Ω) (hγ : γ ∈ Ine (F := E) A)
    (hm : ((y.lpSum u).inePol γ).rootMultiplicity (c γ) ≤ t) (hs : UpperTheory.GalN.SplW c t (y.lpSum u)) :
    UpperTheory.GalN.SplW c t (x.lpSum u) := by
  have kt := killTransfer
  have so := splitOff
  obtain ⟨a, b, e, d, m, p⟩ := hs
  obtain ⟨n, x, rfl⟩ := x.exists_rep
  obtain ⟨n', y, rfl⟩ := y.exists_rep
  obtain ⟨k, u, rfl⟩ := u.exists_rep
  obtain ⟨i, a, rfl⟩ := a.exists_rep
  obtain ⟨j, b, rfl⟩ := b.exists_rep
  rw [e, WD.inePol_of_mem_Ine _ hγ, WD.lpSum_mk, WD.charPol_mk] at hm
  rw [WD.lpSum_mk, WD.lpSum_mk, WD.mk_eq_mk] at e
  obtain ⟨f, f1, f2⟩ := e
  have hbN : b.N = 0 := (WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 m
  have hbc : ∀ s : ↥(Ine (F := E) A), (b.ρ (ineIncl h s)).charpoly = (X - C (c s)) ^ t := fun s => by
    have := p s s.2
    rwa [WD.inePol_of_mem_Ine _ s.2, WD.charPol_mk] at this
  have hb : ∀ (s : ↥(Ine (F := E) A)) v, b.ρ (ineIncl h s) v = c s • v :=
    fun s => UpperTheory.GalN.scalar_of_charpoly (b.semisimple _) (hbc s)
  have hjt : j = t := by simpa using d
  subst hjt
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨(WD.mk x).lpSum (WD.mk u), WD.mk b, ?_, d, m, p⟩
    rw [WD.lpSum_mk, WD.lpSum_mk]
    refine WD.sound ⟨(LinearEquiv.prodUnique (R := ℂ) (M := (Fin n → ℂ) × (Fin k → ℂ)) (M₂ := Fin 0 → ℂ)).symm, fun σ v => ?_, fun v => ?_⟩
    · exact Prod.ext rfl (Subsingleton.elim _ _)
    · exact Prod.ext rfl (Subsingleton.elim _ _)
  let γ' : ↥(Ine (F := E) A) := ⟨γ, hγ⟩
  let q : ℂ[X] := (a.ρ (ineIncl h γ')).charpoly
  have hq0 : q ≠ 0 := (LinearMap.charpoly_monic _).ne_zero
  have hcp : ((y.sum u).ρ (ineIncl h γ')).charpoly = q * (X - C (c γ)) ^ j := by
    rw [WDRep.Iso.charpoly_eq (⟨f, f1, f2⟩ : (y.sum u).Iso (a.sum b)), WDRep.sum_ρ, LinearMap.charpoly_prodMap, hbc γ']
  have hcp2 : ((a.sum b).ρ (ineIncl h γ')).charpoly = q * (X - C (c γ)) ^ j := by
    rw [WDRep.sum_ρ, LinearMap.charpoly_prodMap, hbc γ']
  have hne : q * (X - C (c γ)) ^ j ≠ 0 := mul_ne_zero hq0 ((monic_X_sub_C _).pow _).ne_zero
  have hmult : (q * (X - C (c γ)) ^ j).rootMultiplicity (c γ) = q.rootMultiplicity (c γ) + j := by
    rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow]
  have hq00 : q.rootMultiplicity (c γ) = 0 := by
    have hm' : ((a.sum b).ρ (ineIncl h γ')).charpoly.rootMultiplicity (c γ) ≤ j := hm
    rw [hcp2, hmult] at hm'
    omega
  have hq : q.eval (c γ) ≠ 0 := fun h0 => by
    have := (rootMultiplicity_pos hq0).2 h0
    omega
  have hpol : ∀ s, ((x.sum u).ρ (ineIncl h s)).charpoly = ((y.sum u).ρ (ineIncl h s)).charpoly := fun s => by
    have := hr.pol s
    rw [WD.charPol_mk, WD.charPol_mk] at this
    rw [WDRep.sum_ρ, WDRep.sum_ρ, LinearMap.charpoly_prodMap, LinearMap.charpoly_prodMap, this]
  have hmul : ((x.sum u).ρ (ineIncl h γ')).charpoly.rootMultiplicity (c γ) = j := by
    rw [hpol, hcp, hmult, hq00, zero_add]
  have ha : ∀ v, a.ρ (ineIncl h γ') v = c γ • v → v = 0 := fun v hv => by
    by_contra hv0
    have hev : Module.End.HasEigenvalue (a.ρ (ineIncl h γ')) (c γ) :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
    exact hq ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).1 hev)
  have hz : ∀ v, (y.sum u).ρ (ineIncl h γ') v = c γ • v → (y.sum u).N v = 0 := fun v hv => by
    apply f.injective
    have k1 := f1 (ineIncl h γ') v
    rw [hv, map_smul] at k1
    have k2 : (f v).1 = 0 := ha _ (congrArg Prod.fst k1).symm
    rw [f2, map_zero]
    exact Prod.ext (by simp [k2]) (by simp [hbN])
  have hy : ∀ v, (∀ s, y.ρ (ineIncl h s) v = c s • v) → y.N v = 0 := fun v hv =>
    congrArg Prod.fst (hz (v, 0) (Prod.ext (hv γ') (by simp)))
  have hE : EigZero (WD.mk y) fun s => c s := fun n'' y' e v hv => by
    obtain ⟨g, g1, g2⟩ := WD.mk_eq_mk.1 e
    apply g.injective
    rw [g2, map_zero]
    exact hy _ fun s => by rw [← g1, hv, map_smul]
  have hconj : ∀ (g : Weil h) (s : ↥(Ine (F := E) A)), c (ineConj g s) = c s := fun g s => by
    let v : Fin j → ℂ := fun _ => 1
    have hv : v ≠ 0 := fun hv => one_ne_zero (congrFun hv ⟨0, hj⟩)
    have k1 := hb (ineConj g s) v
    rw [ineIncl_ineConj, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hb s, map_smul,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at k1
    exact smul_left_injective ℂ hv k1.symm
  have hx := hr.eig _ hconj hE n x rfl
  have hqa : aeval (a.ρ (ineIncl h γ')) q = 0 := LinearMap.aeval_self_charpoly _
  have hP : aeval ((a.sum b).ρ (ineIncl h γ')) q = (0 : Module.End ℂ _).prodMap (aeval (b.ρ (ineIncl h γ')) q) := by
    rw [WDRep.sum_ρ, aeval_prodMap', hqa]
  have hP1 : ∀ s : ↥(Ine (F := E) A), ((a.sum b).ρ (ineIncl h s) - c s • 1) * aeval ((a.sum b).ρ (ineIncl h γ')) q = 0 := fun s => by
    rw [hP]
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · simp
    · simp [hb]
  have hP2 : ∀ s : ↥(Ine (F := E) A), aeval ((a.sum b).ρ (ineIncl h γ')) q * ((a.sum b).ρ (ineIncl h s) - c s • 1) = 0 := fun s => by
    rw [hP]
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · simp
    · simp [hb]
  let Φ := f.conjAlgEquiv ℂ
  have hΦ : ∀ σ, Φ ((y.sum u).ρ σ) = (a.sum b).ρ σ := fun σ => LinearMap.ext fun v => by
    obtain ⟨r, rfl⟩ := f.surjective v
    simp only [Φ, LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe]
    exact f1 σ r
  have hZ1 : ∀ s : ↥(Ine (F := E) A), ((y.sum u).ρ (ineIncl h s) - c s • 1) * aeval ((y.sum u).ρ (ineIncl h γ')) q = 0 := fun s =>
    Φ.injective (by rw [map_zero, map_mul, map_sub, map_smul, map_one, ← Polynomial.aeval_algHom_apply, hΦ, hΦ]; exact hP1 s)
  have hZ2 : ∀ s : ↥(Ine (F := E) A), aeval ((y.sum u).ρ (ineIncl h γ')) q * ((y.sum u).ρ (ineIncl h s) - c s • 1) = 0 := fun s =>
    Φ.injective (by rw [map_zero, map_mul, map_sub, map_smul, map_one, ← Polynomial.aeval_algHom_apply, hΦ, hΦ]; exact hP2 s)
  have hT := fun s : ↥(Ine (F := E) A) => kill_mul kt ((x.sum u).ρ.comp (ineIncl h)) ((y.sum u).ρ.comp (ineIncl h))
    (x.sum u).smooth.finite_range (fun r => trace_eq_of_charpoly (hpol r)) s γ' (c s) q
  have hmono : ∀ v, (∀ s : ↥(Ine (F := E) A), (x.sum u).ρ (ineIncl h s) v = c s • v) → (x.sum u).N v = 0 := by
    rintro ⟨v1, v2⟩ hv
    refine Prod.ext (hx v1 fun s => congrArg Prod.fst (hv s)) ?_
    have q2 := congrArg Prod.snd (hv γ')
    have q3 := congrArg Prod.snd (hz (0, v2) (Prod.ext (by simp) q2))
    exact q3
  have hfin := so E Ω A w h _ (x.sum u) c γ' q hq hconj (fun s => (hT s).1 (hZ1 s)) (fun s => (hT s).2 (hZ2 s)) hmono
  have hmul' : ((x.sum u).ρ (ineIncl h γ')).charpoly.rootMultiplicity (c γ') = j := hmul
  rw [hmul'] at hfin
  rw [WD.lpSum_mk]
  exact hfin
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong

namespace UpperTheory.Gal.NearKilling

def TypeRel (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
    ∀ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = a) (θ : Fin (c + 1) → (𝓀[w.adicCompletion E])ˣ →* ℂˣ),
      (∀ b, 0 < d b) → HasTypeVec σ.ρ (stdBlocks d hd) θ →
    ∀ art : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h art →
    ∀ η : Fin (c + 1) → (w.adicCompletion E)ˣ →* ℂˣ, (∀ b, IsTameLift (η b) (θ b)) →
      TrSum r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun i s => ι.symm (η (blockOf d hd i) (art (ineIncl h s)))) ∧
      ∀ b₀, Kills r (fun s : ↥(Ine (F := E) A) => (s : G E Ω)) (fun s => ι.symm (η b₀ (art (ineIncl h s))))
        fun b s => ι.symm (η (b₀.succAbove b) (art (ineIncl h s)))

def GoodLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ → ∀ w : HeightOneSpectrum (𝓞 E),
    ∃ (X : UnramifiedFromSplittingCriterion.Fld E Ω) (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .good l P χ' ∧
      (∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ g ∈ Dec (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) X.K g) ∧
        ∀ w' : HeightOneSpectrum (𝓞 X.K), IsPlaceOver A w' → IsSplitAt w') ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

def AllLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime],
    1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), InScope .all l π χ →
    ∀ S : Set (HeightOneSpectrum (𝓞 E)), (∀ u ∉ S, ∃ B, (CG.mk π).HasSat u B) → ∀ X : UnramifiedFromSplittingCriterion.Fld E Ω, UnramifiedFromSplittingCriterion.Tower S X →
    ∃ (P : CuspSub X.K a) (χ' : HChar (maximalRealSubfield X.K)),
      InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) ({ K := X.K, π := P } : InertialTypesAlt.Pt E Ω a) ∧ InScope .all l P χ' ∧
      ∀ (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Weak π ι r → Weak P ι (r.comp (UpperTheory.V.Af.Bc.res E Ω X.K))

def EigType : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : InertialTypesAlt.Pt E Ω n), InertialTypesAlt.Lifts (InertialTypesAlt.Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)) (h : IsPlaceOver A v)
      (h' : IsPlaceOver A w) (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    (∀ t ∈ Ine (F := E) A, UnramifiedFromSplittingCriterion.Fixes (F := E) Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' → UpperTheory.Zero.LLC.DZ (IrrGL.of τ.ρ τ.smooth τ.irred) →
    ∀ f : ℕ, normV w = g ^ f → (∀ s, HasSupport τ.ρ s → ∀ y ∈ s, y.1 ∣ f) →
    ∀ ξ hξ, InertialTypesAlt.ToralOver h h' (IrrGL.of τ.ρ τ.smooth τ.irred) τ' ξ hξ →
    ∀ rc, UpperTheory.Zero.LLC.IsRecT h rc → ∀ art', IsLocalArtin h' art' →
    ∀ (j : Fin n) (ζ : ↥(Ine (F := E) A) → ℂ),
      (∀ (s : ↥(Ine (F := E) A)) (t : ↥(Ine (F := Y.K) A)), AlgEquiv.restrictScalars E (t : G Y.K Ω) = s →
        ζ s = (ξ j (art' (ineIncl h' t)) : ℂ)) →
      (∀ (x : Weil h) s, ζ (ineConj x s) = ζ s) → EigZero (rc (algNorm τ)) ζ →
      ∃ (c : ℕ) (d : Fin (c + 1) → ℕ) (hd : ∑ b, d b = n) (θ : Fin (c + 1) → (𝓀[w.adicCompletion Y.K])ˣ →* ℂˣ) (b₀ : Fin (c + 1)),
        (∀ b, 0 < d b) ∧ HasTypeVec τ'.ρ (stdBlocks d hd) θ ∧ IsTameLift (ξ j) (θ b₀) ∧ ∀ b, b ≠ b₀ → θ b ≠ θ b₀

def IAT : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
      UpperTheory.Zero.LLC.DZ (IrrGL.of σ.ρ σ.smooth σ.irred) → IneRelInv (wdOf h hl ι r) (rc (algNorm σ))

def IATPol : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope .all l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* w.adicCompletion E), Continuous i →
    ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → ∀ σ, π.IsLocComp w σ →
      UpperTheory.Zero.LLC.DZ (IrrGL.of σ.ρ σ.smooth σ.irred) →
      ∀ s, (wdOf h hl ι r).charPol (ineIncl h s) = (rc (algNorm σ)).charPol (ineIncl h s)

end UpperTheory.Gal.NearKilling
end
end
