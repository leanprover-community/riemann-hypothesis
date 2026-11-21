import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.IdealNormClassCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CokerDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DinfNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.DinfTors
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ExistsGen
import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLen
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ZmodToQZ
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.LenOfCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.layerGen :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (∀ m, (layU l L Ω m).index = l ^ m) ∧
        ∀ γ : G L Ω, IsGen l ⊤ γ → PropA.IsLevel l (cycZ L Ω l γ : ℤ_[l]ˣ) (cZero l L) ∧ γ ∈ levU l ⊤ 1 ∧ ∀ m, IsGen l (layU l L Ω m) (γ ^ l ^ m) := by
  intro L Ω _ _ _ _ _ l _ hmu
  obtain ⟨-, h2, h3, -⟩ := muQ L Ω l
  have hq := h3.1 hmu
  have hr := cycRange L Ω l hmu
  obtain ⟨p1, p2, p3⟩ := princGen l _ hq
  have h0 : ∀ g, cycZ L Ω l g ∈ KStar.TotallyRealRoots.princ l (cZero l L) := fun g => hr ▸ ⟨g, rfl⟩
  have hU : ∀ n, Un L Ω l n = (KStar.TotallyRealRoots.princ l n).comap (cycZ L Ω l) := fun n =>
    Subgroup.ext fun g => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  have h1 : 1 ≤ cZero l L := by
    refine le_trans ?_ hq
    unfold qExp
    split_ifs <;> omega
  refine ⟨fun m => ?_, fun γ hγ => ?_⟩
  · rw [layU, hU, Subgroup.index_comap, hr, p3]
  · have hn : cycZ L Ω l γ ∉ KStar.TotallyRealRoots.princ l (cZero l L + 1) := by
      refine (p1 _ (h0 γ)).1 ?_
      rw [← hr, MonoidHom.range_eq_map]
      exact hγ.2
    obtain ⟨q1, q2⟩ := p2 _ (h0 γ) hn
    refine ⟨q1, ?_, fun m => ⟨?_, ?_⟩⟩
    · have : γ ∈ Un L Ω l 1 := by rw [(h2 1).2 h1]; trivial
      exact this
    · rw [layU, hU, Subgroup.mem_comap, map_pow]
      exact (q2 m).1
    · rw [layU, hU, map_pow]
      exact (Subgroup.map_comap_le _ _).trans
        (((princGen l (cZero l L + m) (hq.trans (Nat.le_add_right _ _))).1 _ (q2 m).1).2 (q2 m).2)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem lu_key (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ)
    [Fact l.Prime] (hmu : HasMuQ l L) (n : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁] [Algebra L₁ Ω]
    [IsScalarTower L L₁ Ω] [IsCyclotomicExtension {l ^ n} L L₁] :
    galOf L L₁ Ω = layU l L Ω (n - cZero l L) ∧ Module.finrank L L₁ = l ^ (n - cZero l L) := by
  haveI : IsAlgClosure L₁ Ω := ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.tower_top (K := L) L₁⟩
  have h1 : galOf L L₁ Ω = Un L Ω l n := by
    rw [galOfCyc L Ω l n L L₁, galOf_self]
  have h2 : Un L Ω l n = layU l L Ω (n - cZero l L) := by
    rcases le_total n (cZero l L) with h | h
    · rw [((muQ L Ω l).2.1 n).2 h, layU, ((muQ L Ω l).2.1 _).2 (by omega)]
    · rw [layU, Nat.add_sub_cancel' h]
  refine ⟨h1.trans h2, ?_⟩
  rw [← (galEmbTop L L₁ Ω).2.2, h1, h2, (layerGen L Ω l hmu).1]

theorem UpperTheory.V.Tower.layerUniq :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (∀ m, IsLayer l m L (layF l L Ω m)) ∧
        (∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁] [Algebra L₁ Ω] [IsScalarTower L L₁ Ω], IsLayer l m L L₁ → galOf L L₁ Ω = layU l L Ω m) ∧
        ∀ (n : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L L₁], IsCyclotomicExtension {l ^ n} L L₁ → IsLayer l (n - cZero l L) L L₁ := by
  intro L Ω _ _ _ _ _ l hl hmu
  refine ⟨fun m => ?_, fun m L₁ _ _ _ _ _ h => ?_, fun n L₁ _ _ _ h => ?_⟩
  · haveI h := (fnCyc L Ω l (cZero l L + m)).1
    refine ⟨⟨_, h⟩, ?_⟩
    have := (lu_key L Ω l hmu (cZero l L + m) (layF l L Ω m)).2
    rwa [Nat.add_sub_cancel_left] at this
  · obtain ⟨⟨k, hk⟩, hf⟩ := h
    obtain ⟨h1, h2⟩ := lu_key L Ω l hmu k L₁
    rw [h1, Nat.pow_right_injective hl.out.two_le (h2.symm.trans hf)]
  · haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
    haveI : FiniteDimensional L L₁ := Module.Finite.of_restrictScalars_finite ℚ L L₁
    let f : L₁ →ₐ[L] Ω := IsAlgClosed.lift
    letI : Algebra L₁ Ω := f.toRingHom.toAlgebra
    haveI : IsScalarTower L L₁ Ω := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
    exact ⟨⟨n, h⟩, (lu_key L Ω l hmu n L₁).2⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.desc :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (U : Subgroup (G k Ω)) [U.Normal], e ≠ 0 → Procyc L Ω l → cycU l U = cycU l (galOf k L Ω) →
        ∃ Φ : Sha D e ≃ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e, IsDesc L D e U Φ.toLinearMap := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _ D e U _ he hpro hcyc
  have hfam := galEmbFam k L Ω l
  have hcycE : ∀ h : G L Ω, cycZ k Ω l (galEmb k L Ω h) = cycZ L Ω l h := fun h => by
    rw [← MonoidHom.comp_apply, hfam.2.2.1]
  have hlift : ∀ σ ∈ galOf k L Ω, ∃ h : G L Ω, galEmb k L Ω h = σ := by
    intro σ hσ
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hσ, by ext x; rfl⟩
  have hmap : Subgroup.map (galEmb k L Ω) (cycU l (⊤ : Subgroup (G L Ω))) = cycU l U := by
    rw [hcyc]
    ext σ
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · intro x
        exact g.commutes x
      · rw [MonoidHom.mem_ker, hcycE]
        exact (Subgroup.mem_inf.1 hg).2
    · intro hσ
      obtain ⟨hσG, hσK⟩ := Subgroup.mem_inf.1 hσ
      obtain ⟨h, rfl⟩ := hlift σ hσG
      refine ⟨h, Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker, ← hcycE]
      exact hσK
  obtain ⟨Ψ, hΨ⟩ := dinfTransport k Ω L Ω (algebraMap k L) (RingEquiv.refl Ω)
    (fun x => IsScalarTower.algebraMap_apply k L Ω x) (galEmb k L Ω) (fun g x => rfl)
    l l U ⊤ hmap
  have hdTw : ∀ (g : G k Ω) (χ : Dinf l l U) (w : cycU l U),
      ((dTw l l U e g χ : Dinf l l U) : cycU l U → QZ l) w =
        (((cycZ k Ω l ^ (-e)) g : ℤ_[l]ˣ) : ℤ_[l]) • (χ : cycU l U → QZ l) (conjHom (cycU l U) g w) := by
    intro g χ w
    rfl
  have hq : ∀ (h : G L Ω) (m : QZ l),
      qzG L Ω l e h m = (((cycZ L Ω l ^ (-e)) h : ℤ_[l]ˣ) : ℤ_[l]) • m := fun h m => rfl
  have hqE : ∀ (h : G L Ω) (m : QZ l),
      (((cycZ k Ω l ^ (-e)) (galEmb k L Ω h) : ℤ_[l]ˣ) : ℤ_[l]) • m = qzG L Ω l e h m := by
    intro h m
    rw [← hfam.2.2.2 e]
    rfl
  have hmemE : ∀ u : cycU l (⊤ : Subgroup (G L Ω)), galEmb k L Ω u ∈ cycU l U := fun u =>
    hmap ▸ Subgroup.mem_map_of_mem _ u.2
  let E : cycU l (⊤ : Subgroup (G L Ω)) → cycU l U := fun u => ⟨galEmb k L Ω u, hmemE u⟩
  have hEsurj : ∀ w : cycU l U, ∃ u, E u = w := by
    intro w
    have hw : (w : G k Ω) ∈ Subgroup.map (galEmb k L Ω) (cycU l (⊤ : Subgroup (G L Ω))) := by
      rw [hmap]
      exact w.2
    obtain ⟨u, hu, huw⟩ := hw
    exact ⟨⟨u, hu⟩, Subtype.ext huw⟩
  have key : ∀ χ : Dinf l l U, χ ∈ ShaD l l U (galOf k L Ω) e ↔
      ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) : cycU l (⊤ : Subgroup (G L Ω)) → QZ l) ∈
        EqHom l (Uinf L Ω l) (qzG L Ω l e) := by
    intro χ
    have hX : ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) : cycU l (⊤ : Subgroup (G L Ω)) → QZ l) ∈
        XDual l (Uinf L Ω l) ℤ_[l] (QZ l) := (Ψ χ).2
    have hΨE : ∀ u, ((Ψ χ : Dinf l l (⊤ : Subgroup (G L Ω))) :
        cycU l (⊤ : Subgroup (G L Ω)) → QZ l) u = (χ : cycU l U → QZ l) (E u) :=
      fun u => hΨ χ u (E u) rfl
    constructor
    · intro hinv
      refine Submodule.mem_inf.2 ⟨hX, (Submodule.mem_iInf _).2 fun h => ?_⟩
      intro u u' huu
      rw [hΨE, hΨE]
      have hg : galEmb k L Ω h ∈ galOf k L Ω := fun x => h.commutes x
      have hinvg := (Representation.mem_invariants _ _).1 hinv ⟨_, hg⟩
      have h2 : ((dTw l l U e (galEmb k L Ω h) χ : Dinf l l U) : cycU l U → QZ l) (E u') =
          (χ : cycU l U → QZ l) (E u') :=
        congrArg (fun y : Dinf l l U => (y : cycU l U → QZ l) (E u')) hinvg
      rw [hdTw] at h2
      have hconj : conjHom (cycU l U) (galEmb k L Ω h) (E u') = E u := by
        apply Subtype.ext
        show (galEmb k L Ω h)⁻¹ * galEmb k L Ω u' * galEmb k L Ω h = galEmb k L Ω u
        rw [← map_inv, ← map_mul, ← map_mul]
        congr 1
        ext x
        show h⁻¹ ((u' : G L Ω) (h x)) = (u : G L Ω) x
        rw [show (u' : G L Ω) (h x) = h ((u : G L Ω) x) from huu x, AlgEquiv.aut_inv,
          AlgEquiv.symm_apply_apply]
      rw [hconj, hqE] at h2
      exact h2.symm
    · intro hE
      obtain ⟨_, hC⟩ := Submodule.mem_inf.1 hE
      rw [Submodule.mem_iInf] at hC
      refine (Representation.mem_invariants _ _).2 fun g => ?_
      obtain ⟨h, hh⟩ := hlift g g.2
      apply Subtype.ext
      funext w
      show ((dTw l l U e (g : G k Ω) χ : Dinf l l U) : cycU l U → QZ l) w = (χ : cycU l U → QZ l) w
      rw [hdTw]
      obtain ⟨u', rfl⟩ := hEsurj w
      have hu : h⁻¹ * (u' : G L Ω) * h ∈ cycU l (⊤ : Subgroup (G L Ω)) := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
          MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 u'.2).2, mul_one, inv_mul_cancel]
      have hcond := hC h ⟨_, hu⟩ u' (fun x => by
        show (u' : G L Ω) (h x) = h ((h⁻¹ * (u' : G L Ω) * h) x)
        rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply])
      rw [hΨE, hΨE] at hcond
      have hconj : conjHom (cycU l U) (g : G k Ω) (E u') = E ⟨_, hu⟩ := by
        apply Subtype.ext
        show (g : G k Ω)⁻¹ * galEmb k L Ω u' * (g : G k Ω) = galEmb k L Ω (h⁻¹ * (u' : G L Ω) * h)
        rw [← hh, map_mul, map_mul, map_inv]
      rw [hconj, ← hh, hqE]
      exact hcond.symm
  have hR : ∀ x : Sha D e, resInf D e (x : H1 (qzTw D e)) ∈ EqHom l (Uinf L Ω l) (qzG L Ω l e) := by
    intro x
    rw [← resInfOnto L Ω l D e he hpro]
    exact Submodule.mem_map_of_mem x.2
  have hED : ∀ f, f ∈ EqHom l (Uinf L Ω l) (qzG L Ω l e) → f ∈ Dinf l l (⊤ : Subgroup (G L Ω)) :=
    fun f hf => (Submodule.mem_inf.1 hf).1
  let R0 : Sha D e →ₗ[ℤ_[l]] Dinf l l (⊤ : Subgroup (G L Ω)) :=
    LinearMap.codRestrict _ ((resInf D e).comp (Sha D e).subtype) (fun x => hED _ (hR x))
  let f : Sha D e →ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e :=
    LinearMap.codRestrict _ (Ψ.symm.toLinearMap.comp R0) (fun x => (key _).2 (by
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hR x))
  have hfinj : Function.Injective f := by
    intro x y hxy
    have h1 : Ψ.symm (R0 x) = Ψ.symm (R0 y) := congrArg Subtype.val hxy
    have h2 : R0 x = R0 y := Ψ.symm.injective h1
    have h3 : resInf D e x = resInf D e y := congrArg Subtype.val h2
    exact Subtype.ext (resInfInj L Ω l D e he hpro h3)
  have hfsurj : Function.Surjective f := by
    intro χ
    have hm := (key (χ : Dinf l l U)).1 χ.2
    rw [← resInfOnto L Ω l D e he hpro] at hm
    obtain ⟨x, hx, hxe⟩ := hm
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    show Ψ.symm (R0 ⟨x, hx⟩) = χ
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hxe
  refine ⟨LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩, ?_⟩
  intro x u u' hu
  show ((Ψ.symm (R0 x) : Dinf l l U) : cycU l U → QZ l) u' = resInf D e x u
  rw [← hΨ (Ψ.symm (R0 x)) u u' hu, LinearEquiv.apply_symm_apply]
  rfl
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.shaDGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U V : Subgroup (G k Ω)) [U.Normal] (e : ℤ) (γ : G k Ω), IsClosed (U : Set (G k Ω)) → V ≤ U → IsGen l V γ →
        ShaD l N U V e = LinearMap.ker (dTw l N U e γ - 1) ∧ ShaD l N U V e = LinearMap.ker (dTw l N U e γ⁻¹ - 1) := by
  intro k Ω _ _ _ _ _ l hl N U V _ e γ hU hVU hγ
  have key : ∀ φ : Dinf l N U, dTw l N U e γ φ = φ → ∀ v ∈ V, dTw l N U e v φ = φ := by
    intro φ hφ v hv
    obtain ⟨n, hn⟩ := (dinfNil k Ω l N U hU φ.1 φ.2).1
    obtain ⟨r, hr⟩ := (dinfTors k Ω l N U).1 hU φ
    have hlev : ∀ w ∈ U, cycZ k Ω l w ∈ KStar.TotallyRealRoots.princ l (max n r) → dTw l N U e w φ = φ := by
      intro w hw hc
      have h1 : dRep l N U w φ = φ :=
        Subtype.ext (hn w ⟨hw, KStar.TotallyRealRoots.princ_anti (le_max_left n r) hc⟩)
      have h2 : cycZ k Ω l w ^ (-e) ∈ KStar.TotallyRealRoots.princ l r :=
        Subgroup.zpow_mem _ (KStar.TotallyRealRoots.princ_anti (le_max_right n r) hc) _
      rw [KStar.TotallyRealRoots.mem_princ] at h2
      obtain ⟨c, hc'⟩ := h2
      rw [dTw_apply, LinearMap.smul_apply, h1, sub_eq_iff_eq_add.1 hc', add_smul, one_smul, mul_comm, mul_smul, hr,
        smul_zero, zero_add]
    have hz : ∀ j : ℤ, dTw l N U e (γ ^ j) φ = φ := by
      intro j
      let S : Subgroup (G k Ω) :=
        { carrier := {g | dTw l N U e g φ = φ}
          mul_mem' := fun {a b} ha hb => by
            show dTw l N U e (a * b) φ = φ
            rw [map_mul, Module.End.mul_apply, show dTw l N U e b φ = φ from hb]; exact ha
          one_mem' := by
            show dTw l N U e 1 φ = φ
            rw [map_one]; rfl
          inv_mem' := fun {a} ha => by
            show dTw l N U e a⁻¹ φ = φ
            conv_lhs => rw [← show dTw l N U e a φ = φ from ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
      exact S.zpow_mem (show γ ∈ S from hφ) j
    have hcl : cycZ k Ω l v ∈ closure ((Subgroup.zpowers (cycZ k Ω l γ) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) :=
      hγ.2 ⟨v, hv, rfl⟩
    have hop : IsOpen ((fun x : ℤ_[l]ˣ => x⁻¹ * cycZ k Ω l v) ⁻¹' (KStar.TotallyRealRoots.princ l (max n r) : Set ℤ_[l]ˣ)) :=
      (KStar.TotallyRealRoots.isOpen_princ _).preimage (by fun_prop)
    obtain ⟨x, hx, j, rfl⟩ := mem_closure_iff.1 hcl _ hop (by simp [one_mem])
    have h3 := hlev ((γ ^ j)⁻¹ * v) (U.mul_mem (U.inv_mem (U.zpow_mem (hVU hγ.1) j)) (hVU hv))
      (by rw [map_mul, map_inv, map_zpow]; exact hx)
    have h4 : v = γ ^ j * ((γ ^ j)⁻¹ * v) := by group
    rw [h4, map_mul, Module.End.mul_apply, h3, hz]
  constructor
  · ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    exact ⟨fun h => h ⟨γ, hγ.1⟩, fun h v => key φ h v.1 v.2⟩
  · ext φ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.End.one_apply]
    refine ⟨fun h => h ⟨γ⁻¹, V.inv_mem hγ.1⟩, fun h v => key φ ?_ v.1 v.2⟩
    conv_lhs => rw [← h]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.existsGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → (l ≠ 2 ∨ U ≤ gamU l ⊤) → ∃ γ, IsGen l U γ := by
  intro k Ω _ _ _ _ _ l _ U hU hcond
  have hclosed : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hU.isCompact.image (continuous_cycZ k Ω l)).isClosed
  have hc : l ≠ 2 ∨ U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l 2 := by
    by_cases hl : l = 2
    · rcases hcond with h | h
      · exact absurd hl h
      · right
        rw [Subgroup.map_le_iff_le_comap]
        intro x hx
        have hx' := h hx
        simp only [gamU, levU, qExp, if_pos hl, Subgroup.mem_inf] at hx'
        exact hx'.2
    · exact Or.inl hl
  obtain ⟨γ', hγ', hle⟩ := UpperTheory.V.Kum.existsGen l (U.map (cycZ k Ω l)) hclosed hc
  obtain ⟨γ, hγU, rfl⟩ := Subgroup.mem_map.mp hγ'
  exact ⟨γ, hγU, hle⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.genGal :
    ∀ (k L Ω : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Field Ω] [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure k Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], IsClosed (galOf k L Ω : Set (G k Ω)) ∧ (Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤) ∧
        (Procyc L Ω l → ∃ γ, IsGen l (galOf k L Ω) γ) := by
  intro k L Ω _ _ _ _ _ _ _ _ _ _ _ l _
  have hcl : IsClosed (galOf k L Ω : Set (G k Ω)) :=
    Subgroup.isClosed_of_isOpen _ (galEmbTop k L Ω).2.1
  have hχ : ∀ g : G L Ω, cycZ k Ω l (galEmb k L Ω g) = cycZ L Ω l g := fun g =>
    DFunLike.congr_fun (galEmbFam k L Ω l).2.2.1 g
  have hiff : Procyc L Ω l ↔ l ≠ 2 ∨ galOf k L Ω ≤ gamU l ⊤ := by
    by_cases h : l = 2
    · subst h
      refine or_congr_right ?_
      rw [← range_galEmb]
      constructor
      · rintro h _ ⟨g, rfl⟩
        refine ⟨trivial, ?_⟩
        show cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2
        rw [hχ]
        exact h g
      · intro h g
        have h' : cycZ k Ω 2 (galEmb k L Ω g) ∈ KStar.TotallyRealRoots.princ 2 2 := (h ⟨g, rfl⟩).2
        rw [hχ] at h'
        exact h'
    · exact ⟨fun _ => Or.inl h, fun _ => Or.inl h⟩
  exact ⟨hcl, hiff, fun h => UpperTheory.V.Tower.existsGen k Ω l _ hcl (hiff.1 h)⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

private theorem span_of_length_le {A : Type} [CommRing A] (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module A V], Module.length A V ≤ n →
      ∃ s : Fin n → V, Submodule.span A (Set.range s) = ⊤ := by
  induction n with
  | zero =>
    intro V _ _ h
    have h0 : Module.length A V = 0 := by simpa using h
    have : Subsingleton V := Module.length_eq_zero_iff.1 h0
    exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro V _ _ h
    rcases subsingleton_or_nontrivial V with hV | hV
    · exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    set P : Submodule A V := Submodule.span A {v} with hP
    have hadd : Module.length A V = Module.length A P + Module.length A (V ⧸ P) :=
      Module.length_eq_add_of_exact P.subtype P.mkQ P.injective_subtype P.mkQ_surjective
        (LinearMap.exact_subtype_mkQ P)
    have hP1 : 1 ≤ Module.length A P := by
      rw [Order.one_le_iff_ne_zero, Ne, Module.length_eq_zero_iff]
      intro hs
      exact hv (congrArg Subtype.val (Subsingleton.elim
        (⟨v, Submodule.mem_span_singleton_self v⟩ : P) 0))
    have hq : Module.length A (V ⧸ P) ≤ n := by
      have h2 : Module.length A (V ⧸ P) + 1 ≤ (n : ℕ∞) + 1 := by
        calc Module.length A (V ⧸ P) + 1 ≤ Module.length A (V ⧸ P) + Module.length A P := by gcongr
          _ = Module.length A V := by rw [hadd, add_comm]
          _ ≤ (n : ℕ∞) + 1 := by simpa using h
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h2
    obtain ⟨t, ht⟩ := ih (V ⧸ P) hq
    choose s hs using fun i => P.mkQ_surjective (t i)
    refine ⟨Fin.cons v s, ?_⟩
    rw [Fin.range_cons, Submodule.span_insert, ← hP, ← Submodule.map_mkQ_eq_top, Submodule.map_span,
      ← Set.range_comp, ← ht]
    congr 2
    exact funext hs

theorem UpperTheory.V.Tower.genDual :
    ∀ (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] (R : ℕ), (∀ m : M, ∃ r : ℕ, (l : ℤ_[l]) ^ r • m = 0) →
        (GenLE ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) R ↔ Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] M (l : ℤ_[l])) ≤ R) := by
  intro l _ M _ _ R hM
  have hc := UpperTheory.V.Tower.cokerDual l M ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] M))
    ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l))) (fun x φ => by simp)
  have hk : LinearMap.ker ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] M))
      = Submodule.torsionBy ℤ_[l] M (l : ℤ_[l]) := by
    ext m; simp
  rw [hk] at hc
  rw [← hc]
  constructor
  · intro h
    exact UpperTheory.V.PropA.cokL l _ R h
  · intro h
    set I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l])} with hI
    haveI : IsPrecomplete I ℤ_[l] := by
      rw [hI, ← PadicInt.maximalIdeal_eq_span_p]
      infer_instance
    haveI : IsHausdorff I (M →ₗ[ℤ_[l]] QZ l) := by
      refine ⟨fun x hx => LinearMap.ext fun m => ?_⟩
      obtain ⟨r, hr⟩ := hM m
      have h1 := hx r
      rw [SModEq.zero, hI, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
        Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨y, -, rfl⟩ := h1
      rw [LinearMap.smul_apply, ← map_smul, hr, map_zero, LinearMap.zero_apply]
    set N : Submodule ℤ_[l] (M →ₗ[ℤ_[l]] QZ l) :=
      LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] (M →ₗ[ℤ_[l]] QZ l))) with hN
    have hNI : N = I • (⊤ : Submodule ℤ_[l] (M →ₗ[ℤ_[l]] QZ l)) := by
      ext x
      rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, hN]
      simp
    obtain ⟨t, ht⟩ := span_of_length_le R ((M →ₗ[ℤ_[l]] QZ l) ⧸ N) h
    choose s hs using fun i => N.mkQ_surjective (t i)
    have h2 : Submodule.span ℤ_[l] (Set.range s) = ⊤ := by
      refine (UpperTheory.V.abelian₂.nakayama ℤ_[l] I _).1 R s ?_
      rw [← hNI, sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp, ← ht]
      congr 2
      exact funext hs
    refine ⟨Fintype.linearCombination ℤ_[l] s, ?_⟩
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, h2]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.genIff :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G k Ω)) (R : ℕ), IsClosed (U : Set (G k Ω)) → (GenLE ℤ_[l] (Xinf l N U) R ↔ xRank l N U ≤ R) := by
  intro k Ω _ _ _ _ _ l _ N U R hU
  exact UpperTheory.V.Tower.genDual l (Dinf l N U) R ((UpperTheory.V.Tower.dinfTors k Ω l N U).1 hU)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

noncomputable section

namespace UpperTheory.V.Tower

section Step0

variable {l : ℕ} [Fact l.Prime] {L₀ : Type} [Field L₀] [NumberField L₀] {Ω : Type} [Field Ω] [Algebra L₀ Ω] [IsAlgClosure L₀ Ω]

theorem step0 (hμ : HasMuQ l L₀) {γ : G L₀ Ω} (hγ : IsGen l ⊤ γ) {e : ℤ} (he : e ≠ 0) (m : ℕ) (L₁ : Type) [Field L₁]
    [NumberField L₁] [Algebra L₀ L₁] (hL : IsLayer l m L₀ L₁) :
    shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ Ω)) e γ ^ l ^ m - 1) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L₀
  haveI : FiniteDimensional L₀ L₁ := Module.Finite.of_restrictScalars_finite ℚ L₀ L₁
  let j : L₁ →ₐ[L₀] Ω := IsAlgClosed.lift
  letI : Algebra L₁ Ω := j.toRingHom.toAlgebra
  haveI : IsScalarTower L₀ L₁ Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Algebra.IsAlgebraic L₀ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure L₁ Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := L₀) L₁⟩
  obtain ⟨D⟩ := Formalism.GaloisCohomology.ldataExists L₁ Ω l
  have hμ₁ : HasMuQ l L₁ := by
    obtain ⟨ζ, hζ⟩ := hμ
    exact ⟨_, hζ.map_of_injective (algebraMap L₀ L₁).injective⟩
  have hU := (layerUniq L₀ Ω l hμ).2.1 m L₁ hL
  obtain ⟨Φ, -⟩ := desc L₀ L₁ Ω l D e ⊤ he ((muQ L₁ Ω l).2.2.2.1 hμ₁).2 (by rw [hU, cycU_levU])
  have hg := ((layerGen L₀ Ω l hμ).2 γ hγ).2.2 m
  rw [← hU] at hg
  rw [← shaLen_eq_shaInv D, shaLen, Φ.length_eq, (shaDGen L₀ Ω l l ⊤ _ e _ isClosed_univ le_top hg).2, ← map_pow]
  exact (cokerDual l _ _ _ fun x φ => by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, xTw_apply_apply]; rfl).symm

variable (l L₀ Ω) in

theorem exists_descends (hμ : HasMuQ l L₀) : ∃ γ : G L₀ Ω, IsGen l ⊤ γ ∧
    PropA.IsLevel l (cycZ L₀ Ω l γ : ℤ_[l]ˣ) (cZero l L₀) ∧ (∃ ζ : L₀, IsPrimitiveRoot ζ (l ^ cZero l L₀)) ∧
    ∀ e : ℕ, 1 ≤ e → ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁], IsLayer l m L₀ L₁ →
      shaInv L₁ l e = cokerLen (xTw l l (⊤ : Subgroup (G L₀ Ω)) e γ ^ l ^ m - 1) := by
  obtain ⟨γ, hγ⟩ := (genGal L₀ L₀ Ω l).2.2 ((muQ L₀ Ω l).2.2.2.1 hμ).2
  rw [galOf_self] at hγ
  exact ⟨γ, hγ, ((layerGen L₀ Ω l hμ).2 γ hγ).1, ((muQ L₀ Ω l).1 _).2 le_rfl, fun e he m L₁ _ _ _ hL =>
    step0 hμ hγ (by omega) m L₁ hL⟩

variable (l L₀) in
theorem isTower_iff (R : ℕ) : IsTower l L₀ R ↔ HasMuQ l L₀ ∧ 1 ≤ R ∧ rankN l L₀ l ≤ R :=
  ⟨fun h => ⟨h.mu, h.pos, (genIff L₀ _ l l ⊤ R isClosed_univ).1 h.gen⟩, fun h =>
    ⟨((muQ L₀ (AlgebraicClosure L₀) l).2.2.2.1 h.1).1, h.1, h.2.1, (genIff L₀ _ l l ⊤ R isClosed_univ).2 h.2.2⟩⟩


end Step0

end UpperTheory.V.Tower

end
end
