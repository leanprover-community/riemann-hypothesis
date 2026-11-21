import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ExactSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.FrameEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.PetInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CapAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IpDef
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.TformPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ContrSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.FnProj
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasXi
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SmSepDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.KugaSucc
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DelCochain
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.LieOneComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SqOrth
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ExactLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CharOf

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section SlopeTestRemainingChoices

open UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem aut_fin (g : GL (Fin a) (Af E)) {φ : Sm E a} (h : GlobalTheory.CuspRep.IsAutForm φ) :
    GlobalTheory.CuspRep.IsAutForm (finRep E a g φ) := by
  have e : Cm.smEq E a (finRep E a g φ) = GroundTheory.Automorphic.AutomorphicForm.rtFin g (Cm.smEq E a φ) :=
    Subtype.ext (funext fun x => (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (x * f g)) Fb.finEmb_eq).symm)
  refine (Cm.isAutForm_iff _).2 ?_
  rw [← Cm.coe_smEq, e]
  exact ((Cm.isAutForm_iff _).1 h).rightTranslate_finEmb g

private theorem char_fin (g : GL (Fin a) (Af E)) {m : (E →+* ℂ) → Multiset ℂ} {φ : Sm E a} (h : Cj.HasChar m φ) :
    Cj.HasChar m (finRep E a g φ) := fun t u => by
  have c : Commute (cap t u) (act (.fin g)) := (S.capAct E a t u).2.1 (.fin g)
  have e : cap t u (finRep E a g φ) = finRep E a g (cap t u φ) := LinearMap.congr_fun c.eq φ
  rw [e, h t u, map_smul]

private theorem sq_fin (ha : 1 ≤ a) (r : ℝ) (g : GL (Fin a) (Af E)) {φ : Sm E a} (h : φ ∈ sqSub E a r) :
    finRep E a g φ ∈ sqSub E a r := by
  have : sqSub E a r ≤ (sqSub E a r).comap (finRep E a g) :=
    Submodule.span_le.2 fun ψ hψ => Submodule.subset_span ((petInv E a ha r).1 g ψ hψ)
  exact this h

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.H.harmSub :
    UpperTheory.V.Cj.H.HarmSub := by
  intro E _ _ _ a ha Ξ r m q
  obtain ⟨L, L1, L2⟩ := (levSub E a Ξ q).2.2
  have comb : ∀ (s : ℂ) (α β : Geo.Co Ξ q), IsH r m α → IsH r m β → IsH r m (s • α + β) := by
    intro s α β hα hβ
    have ap : ∀ X i, cmp i ((s • α + β) X) = s • cmp i (α X) + cmp i (β X) := fun X i => by
      rw [show (s • α + β) X = s • α X + β X from rfl, map_add, map_smul]
    refine ⟨(L1 _).1 (L.add_mem (L.smul_mem s ((L1 _).2 hα.lev)) ((L1 _).2 hβ.lev)),
      by rw [dCo_comb, hα.closed, hβ.closed, smul_zero, add_zero], fun X i => ⟨?_, fun t u => ?_⟩, fun X i => ?_⟩
    · rw [ap]
      exact Cm.mem_range_ofAut.1 (Submodule.add_mem _ (Submodule.smul_mem _ s (Cm.mem_range_ofAut.2 (hα.aut X i).1))
        (Cm.mem_range_ofAut.2 (hβ.aut X i).1))
    · rw [ap, map_add, map_smul, (hα.aut X i).2 t u, (hβ.aut X i).2 t u, smul_add, smul_comm]
    · rw [ap]
      exact Submodule.add_mem _ (Submodule.smul_mem _ s (hα.sq X i)) (hβ.sq X i)
  have zero : IsH r m (0 : Geo.Co Ξ q) := by
    have ap : ∀ X i, cmp i ((0 : Geo.Co Ξ q) X) = 0 := fun X i => map_zero _
    refine ⟨(L1 _).1 L.zero_mem, AlternatingMap.ext fun X => by simp [dCo_apply], fun X i => ⟨?_, fun t u => ?_⟩,
      fun X i => ?_⟩
    · rw [ap]
      exact Cm.mem_range_ofAut.1 (Submodule.zero_mem _)
    · rw [ap, map_zero, smul_zero]
    · rw [ap]
      exact Submodule.zero_mem _
  refine ⟨{ carrier := {ω | IsH r m ω}, add_mem' := ?_, zero_mem' := zero, smul_mem' := ?_ }, fun ω => Iff.rfl, ?_⟩
  · intro α β hα hβ
    have := comb 1 α β hα hβ
    rwa [one_smul] at this
  · intro s α hα
    have := comb s α 0 hα zero
    rwa [add_zero] at this
  · rintro x ω ⟨h1, h2, h3, h4⟩
    refine ⟨(L1 _).1 (L2 x ω ((L1 _).2 h1)), ?_, fun X i => ?_, fun X i => ?_⟩
    · obtain ⟨U, -, -, u3⟩ := h1
      rw [(perNat E a U ⊥ x (fun u hu => by rw [Subgroup.mem_bot.1 hu]; simp) Ξ q ω u3).2.1, h2,
        ← transRep_apply, map_zero]
    · rw [cmp_trans]
      exact ⟨aut_fin x (h3 X i).1, char_fin x (h3 X i).2⟩
    · rw [cmp_trans]
      exact sq_fin ha r x (h4 X i)
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem exists_orthogonal_decomposition_of_isPos {W : Type} [AddCommGroup W] [Module ℂ W] (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ)
    (M : Submodule ℂ W) (hB : IsPos B M) (F K : Submodule ℂ W) (hF : F ≤ M) (hK : K ≤ F)
    [FiniteDimensional ℂ F] (v : W) (hv : v ∈ F) :
    ∃ a ∈ K, ∃ b ∈ F, v = a + b ∧ ∀ x ∈ K, B x b = 0 := by
  letI core : InnerProductSpace.Core ℂ F :=
    { inner := fun x y => B x y
      conj_inner_symm := fun x y => by
        show (starRingEnd ℂ) (B y x) = B x y
        rw [hB.herm]; simp
      re_inner_nonneg := fun x => hB.nonneg x (hF x.2)
      add_left := fun x y z => by
        show B (x + y : F) z = B x z + B y z
        simp
      smul_left := fun x y r => by
        show B (r • x : F) y = (starRingEnd ℂ) r * B x y
        simp
      definite := fun x hx => Subtype.ext (hB.definite x (hF x.2) hx) }
  letI : NormedAddCommGroup F := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore (𝕜 := ℂ) (F := F) inferInstance
  let K' : Submodule ℂ F := K.comap F.subtype
  haveI : CompleteSpace K' := FiniteDimensional.complete ℂ K'
  obtain ⟨y, hy, z, hz, hyz⟩ := K'.exists_add_mem_mem_orthogonal ⟨v, hv⟩
  refine ⟨y, hy, z, z.2, congrArg Subtype.val hyz, fun x hx => ?_⟩
  have := (Submodule.mem_orthogonal K' z).1 hz ⟨x, hK hx⟩ hx
  exact this

private theorem orbit_of_compact_finite_of_open_stabilizer {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (n : W) (U V : Subgroup G)
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVn : ∀ u ∈ V, ρ u n = n) :
    ((fun u => ρ u n) '' (U : Set G)).Finite := by
  obtain ⟨t, ht⟩ := hUc.elim_finite_subcover (fun u : U => (fun g => (u : G)⁻¹ * g) ⁻¹' (V : Set G))
    (fun u => hVo.preimage (continuous_const.mul continuous_id))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp [V.one_mem]⟩)
  apply ((t : Set U).toFinite.image (fun u : U => ρ (u : G) n)).subset
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨u, hu, hgu⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨u, hu, ?_⟩
  have hg' : g = (u : G) * ((u : G)⁻¹ * g) := by group
  show ρ (u : G) n = ρ g n
  rw [hg', map_mul, Module.End.mul_apply, hVn _ hgu]

theorem UpperTheory.V.Cj.H.absSS :
    UpperTheory.V.Cj.H.AbsSS := by
  intro G W _ _ _ _ _ ρ M B hB hM hc hsm hfd N hNM hN
  have hρ : ∀ (g h : G) (x : W), ρ g (ρ h x) = ρ (g * h) x := by
    intro g h x
    rw [map_mul, Module.End.mul_apply]
  let N' : Submodule ℂ W :=
    { carrier := {w | w ∈ M ∧ ∀ n ∈ N, B n w = 0}
      add_mem' := fun {a b} ha hb => ⟨M.add_mem ha.1 hb.1, fun n hn => by simp [ha.2 n hn, hb.2 n hn]⟩
      zero_mem' := ⟨M.zero_mem, fun n _ => by simp⟩
      smul_mem' := fun r w hw => ⟨M.smul_mem r hw.1, fun n hn => by simp [hw.2 n hn]⟩ }
  have memN' : ∀ w, w ∈ N' ↔ w ∈ M ∧ ∀ n ∈ N, B n w = 0 := fun w => Iff.rfl
  refine ⟨N', fun w hw => ((memN' w).1 hw).1, ?_, ?_, ?_⟩
  · intro g w hw
    rw [memN'] at hw ⊢
    refine ⟨hM g w hw.1, fun n hn => ?_⟩
    obtain ⟨c, hcg⟩ := hc g
    have hn' : ρ g⁻¹ n ∈ N := hN _ _ hn
    have h1 : ρ g (ρ g⁻¹ n) = n := by rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← h1, hcg _ (hNM hn') _ hw.1, hw.2 _ hn', mul_zero]
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxN'⟩ := Submodule.mem_inf.1 hx
    rw [memN'] at hxN'
    exact (Submodule.mem_bot ℂ).2 (hB.definite x (hNM hxN) (hxN'.2 x hxN))
  · refine le_antisymm (sup_le hNM fun w hw => ((memN' w).1 hw).1) ?_
    intro v hv
    obtain ⟨U, hUo, hUc, hUv⟩ := hsm v hv
    haveI := hfd U hUo
    have hFM : Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} ≤ M :=
      Submodule.span_le.2 fun x hx => hx.1
    have hFfix : ∀ x ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}, ∀ u ∈ U, ρ u x = x := by
      intro x hx u hu
      induction hx using Submodule.span_induction with
      | mem y hy => exact hy.2 u hu
      | zero => simp
      | add y z _ _ hy hz => simp [hy, hz]
      | smul r y _ hy => simp [hy]
    have hvF : v ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hv, hUv⟩
    obtain ⟨a, haK, b, hbF, hvab, hb⟩ :=
      exists_orthogonal_decomposition_of_isPos B M hB _ (N ⊓ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x}) hFM inf_le_right v hvF
    rw [hvab]
    refine Submodule.add_mem_sup (Submodule.mem_inf.1 haK).1 ((memN' b).2 ⟨hFM hbF, fun n hn => ?_⟩)
    have hinv : ∀ u ∈ U, ∀ x ∈ M, B (ρ u x) b = B x b := by
      intro u hu x hx
      obtain ⟨c, hcu⟩ := hc u
      have h1 := hcu x hx b (hFM hbF)
      rw [hFfix b hbF u hu] at h1
      by_cases hb0 : b = 0
      · simp [hb0]
      have h2 := hcu b (hFM hbF) b (hFM hbF)
      rw [hFfix b hbF u hu] at h2
      have hbb : B b b ≠ 0 := fun h => hb0 (hB.definite b (hFM hbF) h)
      have hc1 : c = 1 := by
        have h3 : (c - 1) * B b b = 0 := by rw [sub_mul, ← h2]; ring
        rcases mul_eq_zero.1 h3 with h | h
        · exact sub_eq_zero.1 h
        · exact absurd h hbb
      rw [h1, hc1, one_mul]
    obtain ⟨V, hVo, -, hVn⟩ := hsm n (hNM hn)
    have hfin := orbit_of_compact_finite_of_open_stabilizer ρ n U V hUc hVo hVn
    have hmemS : ∀ x, x ∈ hfin.toFinset ↔ ∃ g ∈ U, ρ g n = x := by
      intro x
      rw [Set.Finite.mem_toFinset]
      rfl
    have hSN : ∀ x ∈ hfin.toFinset, x ∈ N ∧ B x b = B n b := by
      intro x hx
      obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
      exact ⟨hN g n hn, hinv g hg n (hNM hn)⟩
    have hsN : (∑ x ∈ hfin.toFinset, x) ∈ N := Submodule.sum_mem _ fun x hx => (hSN x hx).1
    have hsfix : ∀ u ∈ U, ρ u (∑ x ∈ hfin.toFinset, x) = ∑ x ∈ hfin.toFinset, x := by
      intro u hu
      rw [map_sum]
      refine Finset.sum_nbij' (fun x => ρ u x) (fun x => ρ u⁻¹ x) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u * g, U.mul_mem hu hg, (hρ u g n).symm⟩
      · intro x hx
        obtain ⟨g, hg, rfl⟩ := (hmemS x).1 hx
        exact (hmemS _).2 ⟨u⁻¹ * g, U.mul_mem (U.inv_mem hu) hg, (hρ u⁻¹ g n).symm⟩
      · intro x _
        rw [hρ, inv_mul_cancel, map_one, Module.End.one_apply]
      · intro x _
        rw [hρ, mul_inv_cancel, map_one, Module.End.one_apply]
    have hsF : (∑ x ∈ hfin.toFinset, x) ∈ Submodule.span ℂ {x | x ∈ M ∧ ∀ u ∈ U, ρ u x = x} :=
      Submodule.subset_span ⟨hNM hsN, hsfix⟩
    have hzero := hb _ (Submodule.mem_inf.2 ⟨hsN, hsF⟩)
    rw [map_sum, LinearMap.sum_apply, Finset.sum_congr rfl fun x hx => (hSN x hx).2,
      Finset.sum_const, nsmul_eq_mul] at hzero
    have hcard : (hfin.toFinset.card : ℂ) ≠ 0 := by
      have : n ∈ hfin.toFinset := (hmemS n).2 ⟨1, U.one_mem, by simp⟩
      exact_mod_cast (Finset.card_pos.2 ⟨n, this⟩).ne'
    exact (mul_eq_zero.1 hzero).resolve_left hcard
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL ComplexOrder
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private noncomputable def ipL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q n : ℕ}
    (e : Fin n → Herm E a)
    (H : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ⋆[ℂ] Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ) : Co Ξ q →ₗ⋆[ℂ] Co Ξ q →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun ω η => ip e H ω η)
    (fun ω ω' η => by
      simp only [ip, AlternatingMap.add_apply, map_add, LinearMap.add_apply, Finset.sum_add_distrib])
    (fun c ω η => by
      simp only [ip, AlternatingMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, Finset.smul_sum])
    (fun ω η η' => by
      simp only [ip, AlternatingMap.add_apply, map_add, Finset.sum_add_distrib])
    (fun c ω η => by
      simp only [ip, AlternatingMap.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply])

private theorem ipL_apply {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q n : ℕ}
    (e : Fin n → Herm E a)
    (H : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ⋆[ℂ] Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ) (ω η : Co Ξ q) :
    ipL e H ω η = ip e H ω η := rfl

theorem UpperTheory.V.Cj.H.coForm :
    UpperTheory.V.Cj.H.CoForm := by
  intro E _ _ _ a ha Ξ r q
  obtain ⟨-, H, hH, hx⟩ := petInv E a ha r
  obtain ⟨n, e, he⟩ := frameEx E a
  have hT := tformPos (Sm E a) Ξ.d H (sqSub E a r) 1 hH Matrix.PosDef.one
  obtain ⟨h1, h2⟩ := ipDef E a n e he _ (tform H 1) _ hT q
  refine ⟨transRep Ξ q, ipL e (tform H 1), fun _ _ => rfl, fun M hM => ⟨fun ω η => h1 ω η, fun ω hω => ?_, fun ω hω => ?_⟩,
    fun x => ?_⟩
  · exact (h2 ω fun X => mem_tens.2 (hM ω hω X)).1
  · exact (h2 ω fun X => mem_tens.2 (hM ω hω X)).2
  · obtain ⟨c, hc⟩ := hx x
    refine ⟨c, fun ω η hω hη => ?_⟩
    rw [ipL_apply, ipL_apply]
    simp only [ip, tform_apply, cmp_trans, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hc _ (hω (fun k => e (I k)) i) _ (hη (fun k => e (I k)) j)
    rw [mul_left_comm, ← this]
    rfl
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : W →ₗ[ℂ] W) (i : Fin d)
    (x : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ x) = T (cmp i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp

private noncomputable def coords {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (q : ℕ)
    {n : ℕ} (e : Fin n → Herm E a) : Co Ξ q →ₗ[ℂ] ((Fin q → Fin n) × Fin Ξ.d → Sm E a) where
  toFun ω p := cmp p.2 (ω fun j => e (p.1 j))
  map_add' α β := funext fun p => map_add (Bor.cmp p.2) _ _
  map_smul' c α := funext fun p => map_smul (Bor.cmp p.2) c _

private theorem coords_inj {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (q : ℕ)
    {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) : Function.Injective (coords Ξ q e) := by
  intro α β h
  have hs : Submodule.span ℝ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 fun X _ => ?_
    rw [he X]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  apply AlternatingMap.coe_multilinearMap_injective
  refine MultilinearMap.ext_of_span_eq_top (g := fun _ => e) (fun _ => hs) fun I => ?_
  change α (fun j => e (I j)) = β (fun j => e (I j))
  rw [← sum_cmp (α _), ← sum_cmp (β _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := congrFun h (I, i)
  exact congrArg (· ⊗ₜ[ℂ] _) this

theorem UpperTheory.V.Cj.H.harmFin :
    UpperTheory.V.Cj.H.HarmFin := by
  intro E _ _ _ a Ξ r m q U hU
  obtain ⟨n, e, he⟩ := frameEx E a
  obtain ⟨W, _, _, _, ρ, hρ, hk⟩ := kType E a Ξ q
  have hF := formsFiniteGL E a U hU W ρ hρ fun t u => ((m t).map (u + ·)).prod
  set F := Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms U ρ fun t u => ((m t).map (u + ·)).prod) with hFd
  have hle : ∀ ω ∈ Submodule.span ℂ {ω : Co Ξ q | IsH r m ω ∧ ∀ u ∈ U, trans u ω = ω}, ∀ p, coords Ξ q e ω p ∈ F := by
    intro ω hω p
    induction hω using Submodule.span_induction with
    | zero => rw [map_zero]; exact F.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact F.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact F.smul_mem c hx
    | mem ω hω =>
      obtain ⟨h, hu⟩ := hω
      obtain ⟨U', -, -, hl⟩ := h.lev
      refine Submodule.subset_span ⟨(h.aut _ _).1, fun k hk' => ?_, fun g => ?_, (h.aut _ _).2⟩
      · have h1 := congrArg (fun η : Co Ξ q => cmp p.2 (η fun j => e (p.1 j))) (hu k hk')
        exact (cmp_rT _ _ _).symm.trans h1
      · obtain ⟨T, w, hT, hw⟩ := hk ω hl.equiv (fun j => e (p.1 j)) p.2
        have := GlobalTheory.Published.AutFinGL.type_of_map ρ T hT w g
        rw [hw] at this
        exact this
  refine FiniteDimensional.of_injective (V₂ := (Fin q → Fin n) × Fin Ξ.d → F)
    (LinearMap.pi fun p => ((LinearMap.proj p ∘ₗ coords Ξ q e) ∘ₗ Submodule.subtype _).codRestrict F fun ω => hle ω.1 ω.2 p)
    fun α β h => Subtype.ext (coords_inj Ξ q he (funext fun p => ?_))
  exact congrArg Subtype.val (congrFun h p)
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem harmSS_fix {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} {ω : Co Ξ q} (h : IsLev U Ξ ω) {u : GL (Fin a) (Af E)} (hu : u ∈ U) :
    trans u ω = ω := by
  ext X
  have hle : Submodule.span ℂ {x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v} ≤
      LinearMap.eqLocus ((act (.fin u) : Module.End ℂ (Sm E a)).rTensor (Fin Ξ.d → ℂ)) LinearMap.id := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, v, hφ, rfl⟩
    show LinearMap.rTensor _ _ (φ ⊗ₜ[ℂ] v) = φ ⊗ₜ[ℂ] v
    rw [LinearMap.rTensor_tmul, hφ.2.1 u hu]
  exact hle (h.val X)

theorem UpperTheory.V.Cj.H.harmSS :
    UpperTheory.V.Cj.H.HarmSS := by
  intro E _ _ _ a ha Ξ r m q M hM hT N hNM hN
  obtain ⟨ρ, B, hρ, hpos, hc⟩ := UpperTheory.V.Cj.H.coForm E a ha Ξ r q
  have hsq : ∀ ω ∈ M, Val (sqSub E a r) ω := fun ω h => ((hM ω).1 h).sq
  obtain ⟨N', h1, h2, h3, h4⟩ := UpperTheory.V.Cj.H.absSS (GL (Fin a) (Af E)) (Co Ξ q) ρ M B (hpos M hsq)
    (fun g v hv => by rw [hρ]; exact hT g v hv)
    (fun g => by
      obtain ⟨c, h⟩ := hc g
      exact ⟨c, fun v hv w hw => by rw [hρ, hρ]; exact h v w (hsq v hv) (hsq w hw)⟩)
    (fun v hv => by
      obtain ⟨U, hUo, hUc, hU⟩ := ((hM v).1 hv).lev
      exact ⟨U, hUo, hUc, fun u hu => by rw [hρ]; exact harmSS_fix hU hu⟩)
    (fun U hU => by
      have h := UpperTheory.V.Cj.H.harmFin E a Ξ r m q U hU
      have e : {v : Co Ξ q | v ∈ M ∧ ∀ u ∈ U, ρ u v = v} = {ω : Co Ξ q | IsH r m ω ∧ ∀ u ∈ U, trans u ω = ω} := by
        ext v
        simp only [Set.mem_setOf_eq, hM, hρ]
      rw [e]
      exact h)
    N hNM (fun g v hv => by rw [hρ]; exact hN g v hv)
  exact ⟨N', h1, fun x ω h => by rw [← hρ]; exact h2 x ω h, h3, h4⟩
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H
open scoped ComplexOrder

theorem UpperTheory.V.Cj.H.casB :
    UpperTheory.V.Cj.H.CasB := by
  intro E _ _ _ a n e he Ξ r
  obtain ⟨c, hc⟩ := casXi E a n e he Ξ (-r)
  obtain ⟨G, hG, hadj⟩ := admEx E a Ξ
  have hell : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), ell E a (toL (star X)) = ell E a (toL X) := fun X => by
    show (∑ w : InfinitePlace E, ∑ i, ((star X) i i w).re) / _ = (∑ w : InfinitePlace E, ∑ i, (X i i w).re) / _
    simp [Matrix.star_apply]
  have hS : ∀ X : Matrix (Fin a) (Fin a) (Cinf E),
      (shift Ξ.dmat (-r) (toL X))ᴴ * G = G * shift Ξ.dmat (-r) (toL (star X)) := fun X => by
    rw [shift_apply, shift_apply, hell, conjTranspose_add, add_mul, mul_add, hadj, conjTranspose_smul,
      conjTranspose_one, star_trivial (_ : ℝ), smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hQ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E),
      (shift Ξ.dmat (-r) (toL X) * shift Ξ.dmat (-r) (toL X))ᴴ * G =
        G * (shift Ξ.dmat (-r) (toL (star X)) * shift Ξ.dmat (-r) (toL (star X))) := fun X => by
    rw [conjTranspose_mul, mul_assoc, hS, ← mul_assoc, hS, mul_assoc]
  have h : (cas (shift Ξ.dmat (-r)) e)ᴴ * G = G * cas (shift Ξ.dmat (-r)) e := by
    unfold cas
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : star (e j).1 = (e j).1 := (e j).2
    have h2 : star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := by
      rw [star_smul, h1]; simp
    have h3 : toL (-(Complex.I • (e j).1)) = -toL (Complex.I • (e j).1) := rfl
    rw [conjTranspose_sub, sub_mul, hQ, hQ, h1, h2, h3, map_neg, neg_mul_neg, mul_sub]
  rw [hc, conjTranspose_smul, conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  refine ⟨c.re, ?_⟩
  unfold HasCas
  rw [hc]
  ext i j
  have hi := congrFun (congrFun h i) i
  have hp : G i i ≠ 0 := (hG.diag_pos (i := i)).ne'
  simp only [Matrix.smul_apply, smul_eq_mul] at hi
  have hs : star c = c := mul_right_cancel₀ hp hi
  rw [← Complex.conj_eq_iff_re.1 hs]
  simp
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem rT_map_on {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (N : Submodule ℂ W) (T A : Module.End ℂ W)
    (B : Module.End ℂ (Fin d → ℂ)) (h : ∀ φ ∈ N, A (T φ) = T (A φ)) (m : W ⊗[ℂ] (Fin d → ℂ)) (hm : ∀ i, cmp i m ∈ N) :
    T.rTensor _ (TensorProduct.map A B m) = TensorProduct.map A B (T.rTensor _ m) := by
  rw [← sum_cmp m]
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.map_tmul]
  exact Finset.sum_congr rfl fun i _ => by rw [h _ (hm i)]

private theorem rT_smLie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a)
    (N : Submodule ℂ (Sm E a)) (T : Module.End ℂ (Sm E a)) (hT : IsOp N T) (X : Lie E a)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (hm : ∀ i, cmp i m ∈ N) :
    smLie Ξ X (T.rTensor _ m) = T.rTensor _ (smLie Ξ X m) := by
  have h1 := rT_map_on N T (lie E a X) LinearMap.id (hT.lie X) m hm
  have h2 := rT_map_on N T LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (fun _ _ => rfl) m hm
  change TensorProduct.map (lie E a X) LinearMap.id (T.rTensor _ m) +
      TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) (T.rTensor _ m) =
    T.rTensor _ (TensorProduct.map (lie E a X) LinearMap.id m + TensorProduct.map LinearMap.id (Matrix.toLin' (Ξ.dmat X)) m)
  rw [map_add, h1, h2]

theorem UpperTheory.V.Cj.H.appFacts :
    UpperTheory.V.Cj.H.AppFacts := by
  intro E _ _ _ a U Ξ r hr N hN T hT q ω hω hv
  obtain ⟨-, -, hl, hc⟩ := levLin E a U Ξ q
  have hone : ∀ X i, ∀ m : ℂ, Ξ.dmat (oneL E a) = m • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) →
      lie E a (oneL E a) (T (cmp i (ω X))) = -m • T (cmp i (ω X)) := fun X i m hm => by
    rw [hT.lie _ _ (hv X i), (hl ω hω X i).2.2 m hm, map_smul]
  have hsq : ∀ X i, IsSq r (T (cmp i (ω X))) := fun X i => hN.sq _ (hT.maps _ (hv X i)) (hone X i _ hr)
  refine ⟨⟨?_, fun X i h => ?_, fun X => mem_span_of_cmp fun i => ?_⟩, fun X i => ?_, fun X i => ?_, ?_⟩
  · intro k X
    rw [app_apply, app_apply, hω.equiv k X]
    exact rT_map_on N T _ _ (hT.rt _) _ (hv X)
  · rw [app_apply, hω.basic X i h, map_zero]
  · rw [hc]
    refine ⟨(hsq X i).left, fun u hu => ?_, hone X i⟩
    exact (hT.rt _ _ (hv X i)).trans (congrArg T ((hl ω hω X i).2.1 u hu))
  · rw [hc]
    exact hT.maps _ (hv X i)
  · rw [hc]
    exact Submodule.subset_span (hsq X i)
  · refine AlternatingMap.ext fun X => ?_
    rw [app_apply]
    simp only [dCo, AlternatingMap.alternatizeUncurryFin_apply, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
    exact rT_smLie Ξ N T hT _ _ (hv _)
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem kugaSm_map {E : Type} [Field E] {a n : ℕ} (e : Fin n → Herm E a) {A A' : Type} [Ring A] [Module ℝ A]
    [Ring A'] [Module ℝ A'] (f : A →+* A') (L : Lie E a →ₗ[ℝ] A) (L' : Lie E a →ₗ[ℝ] A') (h : ∀ X, L' X = f (L X)) :
    cas L' e = f (cas L e) := by
  simp only [cas, map_sum, map_sub, map_mul, h]

private theorem kugaSm_A {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r : ℝ) :
    cas (shift (smA Ξ) r) e = (cas (shift (lie E a) r) e).rTensor (Fin Ξ.d → ℂ) := by
  refine kugaSm_map e (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)).toRingHom _ _ fun X => ?_
  change _ = (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)) _
  rw [shift_apply, shift_apply, map_add, ← algebraMap_smul ℂ (r * ell E a X) (1 : Module.End ℂ (Sm E a)), map_smul, map_one,
    algebraMap_smul]
  rfl

private theorem kugaSm_B {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r c : ℝ) (h : HasCas Ξ r c e) :
    cas (shift (smB Ξ) (-r)) e = (c : ℂ) • 1 := by
  let f : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
    (Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) (Sm E a)).comp
      (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have h1 : cas (shift (smB Ξ) (-r)) e = f (cas (shift Ξ.dmat (-r)) e) := by
    refine kugaSm_map e f.toRingHom _ _ fun X => ?_
    change _ = f _
    rw [shift_apply, shift_apply, map_add, ← algebraMap_smul ℂ (-r * ell E a X) (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), map_smul,
      map_one, algebraMap_smul, smB_apply]
    rfl
  rw [h1, show cas (shift Ξ.dmat (-r)) e = _ from h, map_smul, map_one]

theorem UpperTheory.V.Cj.H.kugaSm :
    UpperTheory.V.Cj.H.KugaSm := by
  intro E _ _ _ a n e he Ξ r c hc
  obtain ⟨a1, b1, hab, -, -, hinf⟩ := smAB E a Ξ
  obtain ⟨-, -, -, l4⟩ := ellFacts E a
  have hA := l4 _ _ r a1
  have hB := l4 _ _ (-r) b1
  have hsum : shift (smA Ξ) r + shift (smB Ξ) (-r) = smLie Ξ := by
    rw [shift_add_shift]
    exact LinearMap.ext fun X => add_sub_cancel (smA Ξ X) (smLie Ξ X)
  have hcom : ∀ X Y, Commute (shift (smA Ξ) r X) (shift (smB Ξ) (-r) Y) := fun X Y => by
    rw [shift_apply, shift_apply]
    exact ((hab X Y).add_right ((Commute.one_right _).smul_right _)).add_left ((Commute.one_left _).smul_left _)
  have hcas : cas (shift (smB Ξ) (-r)) e - cas (shift (smA Ξ) r) e = -(casA r c e).rTensor (Fin Ξ.d → ℂ) := by
    rw [kugaSm_A, kugaSm_B e Ξ r c hc, casA, LinearMap.rTensor_sub, LinearMap.rTensor_smul, neg_sub, Module.End.one_eq_id,
      Module.End.one_eq_id, LinearMap.rTensor_id]
  have hdel : ∀ (q : ℕ) (X : Fin q → Herm E a),
      del (shift (smB Ξ) (-r) - shift (smA Ξ) r) e (0 : Co Ξ (q + 1)) X = 0 := fun q X => by
    simp [del_apply]
  refine ⟨fun ω hω hd => ?_, fun q ω hω hd => ?_⟩
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaZero E a n e _ _ _ hcom ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply] at h
    rw [app_apply]
    exact neg_eq_zero.1 h.symm
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaSucc E a n e he _ _ _ hA hB hcom q ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply, add_zero] at h
    rw [app_apply, AlternatingMap.neg_apply]
    exact (neg_eq_iff_eq_neg.1 h.symm)
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem lie_left (X : Lie E a) (φ : Sm E a) (h g : GA E a) (hφ : ∀ g, φ.1 (h * g) = φ.1 g) :
    (lie E a X φ).1 (h * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (h * g) =ᶠ[nhds (oneL E a)] chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    obtain ⟨u, hu⟩ := hx
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, chart_val, mul_assoc, hφ]
  change fderiv ℝ (chart φ.1 (h * g)) (oneL E a) X = fderiv ℝ (chart φ.1 g) (oneL E a) X
  rw [e.fderiv_eq]

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem level_lie {U : Subgroup (GL (Fin a) (Af E))} {Ξ : AlgRep E a} (X : Lie E a) (φ : Sm E a)
    (h : IsLevelFn U Ξ φ) : IsLevelFn U Ξ (lie E a X φ) := by
  refine ⟨fun γ g => lie_left X φ _ g (h.1 γ), fun u hu => ?_, fun m hm => ?_⟩
  · exact (LinearMap.congr_fun (lie_rt_fin X u) φ).symm.trans (congrArg (lie E a X) (h.2.1 u hu))
  · rw [lie_one_comm, h.2.2 m hm, map_smul]

private theorem adj_span (Ξ : AlgRep E a) (r : ℝ) (P : Sm E a → Prop) (hP : ∀ X φ, P φ → P (lie E a X φ)) (X : Lie E a)
    (m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v}) :
    smAdj Ξ r X m ∈ Submodule.span ℂ {x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ) | ∃ φ v, P φ ∧ x = φ ⊗ₜ[ℂ] v} := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    rw [smAdj, adj_apply, smA_apply, smB_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, _, hφ, rfl⟩)
      (Submodule.subset_span ⟨_, _, hP X φ hφ, rfl⟩))
      (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨_, _, hφ, rfl⟩))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

private theorem k_adj (Ξ : AlgRep E a) (r : ℝ) (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    smK Ξ k * smAdj Ξ r (toL X) = smAdj Ξ r (toL (k.1 * X * star k.1)) * smK Ξ k := by
  obtain ⟨-, -, -, hA, hB, -⟩ := smAB E a Ξ
  refine LinearMap.ext fun m => ?_
  have h1 := LinearMap.congr_fun (hA k X) m
  have h2 := LinearMap.congr_fun (hB k X) m
  simp only [Module.End.mul_apply] at h1 h2 ⊢
  rw [smAdj, adj_apply, adj_apply, map_sub, map_sub, h1, h2, (ellFacts E a).2.2.1 k X, LinearMap.map_smul_of_tower]

end

theorem UpperTheory.V.Cj.H.delLev :
    UpperTheory.V.Cj.H.DelLev := by
  intro E _ _ _ a n e he U Ξ r q ω
  refine ⟨fun h => ⟨delCochain E a n e he _ _ _ (fun k X => k_adj Ξ r k X.1) q ω h.equiv, fun X i hi => ?_, fun X => ?_⟩,
    fun h X => ?_⟩
  · rw [del_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h.basic (Matrix.vecCons (e j) X) i.succ hi, map_zero]
  · rw [del_apply]
    exact Submodule.sum_mem _ fun j _ => adj_span Ξ r _ level_lie _ _ (h.val _)
  · refine mem_tens.1 (span_le_tens (P := fun φ => φ ∈ sqSub E a r) (fun _ h => h) ?_)
    rw [del_apply]
    exact Submodule.sum_mem _ fun j _ => adj_span Ξ r _ ((sqLie E a r).2) _ _ (mem_span_of_cmp (h _))
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.resExact :
    UpperTheory.V.Cj.H.ResExact := by
  intro E _ _ _ a ha n e he U Ξ r c hc q ω hω hd
  obtain ⟨k0, k1⟩ := kugaSm E a n e he Ξ r c hc
  cases q with
  | zero => exact ⟨k0 ω hω.equiv hd, fun _ _ => trivial⟩
  | succ q =>
    have hk := k1 q ω hω.equiv hd
    obtain ⟨d1, d2⟩ := delLev E a n e he U Ξ r q ω
    obtain ⟨l1, l2, -⟩ := levLin E a U Ξ q
    have hl := d1 hω
    refine ⟨⟨(-1 : ℂ) • del (smAdj Ξ r) e ω + (0 : ℂ) • del (smAdj Ξ r) e ω, l1 _ _ _ _ hl hl, ?_⟩, fun hs h0 => ?_⟩
    · rw [l2, hk, zero_smul, add_zero]
      exact AlternatingMap.ext fun X => neg_one_smul ℂ _
    · rw [hk, neg_eq_zero] at h0
      exact (sqOrth E a ha n e he Ξ r q).2 ω hs (d2 hs) h0
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem co_ext {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    {α β : Co Ξ q} (h : ∀ X i, cmp i (α X) = cmp i (β X)) : α = β := by
  refine AlternatingMap.ext fun X => ?_
  rw [← sum_cmp (α X), ← sum_cmp (β X)]
  exact Finset.sum_congr rfl fun i _ => by rw [h X i]

private theorem app_zero' {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a} {q : ℕ}
    (T : Module.End ℂ (Sm E a)) : app T (0 : Co Ξ q) = 0 :=
  AlternatingMap.ext fun X => by
    rw [app_apply, AlternatingMap.zero_apply, map_zero]

private theorem hasLev_of {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {φ : Sm E a}
    (h : ∀ u ∈ U, act (.fin u) φ = φ) : HasLev φ := by
  refine isOpen_iff_forall_mem_open.2 fun k hk => ⟨(fun x => k⁻¹ * x) ⁻¹' U, fun x hx => ?_,
    hU.preimage (continuous_const.mul continuous_id), by simp⟩
  have e1 : finRep E a (k⁻¹ * x) φ = φ := h _ hx
  have e2 : finRep E a k φ = φ := hk
  change finRep E a x φ = φ
  have e3 : x = k * (k⁻¹ * x) := by simp
  rw [e3, map_mul, Module.End.mul_apply, e1, e2]

private theorem locLim_sub {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {f : ℕ → Sm E a} {φ : Sm E a}
    (h : LocLim f φ) : LocLim (fun k => f k - φ) 0 := by
  intro C hC
  have := h C hC
  rw [Metric.tendstoUniformlyOn_iff] at this ⊢
  intro ε hε
  filter_upwards [this ε hε] with k hk x hx
  have e := hk x hx
  change dist (0 : ℂ) ((f k).1 x - φ.1 x) < ε
  rwa [dist_comm, dist_zero_right, ← dist_eq_norm, dist_comm]

theorem UpperTheory.V.Cj.H.hodgeEx :
    UpperTheory.V.Cj.H.HodgeEx := by
  intro E _ _ _ a ha n e he U hUo hUc Ξ r hr q α hα hd hs
  obtain ⟨c, hc⟩ := casB E a n e he Ξ r
  obtain ⟨N, P, Q, S, hN, hR⟩ := fnProj E a ha r n e he c
  obtain ⟨l1, -, l3, l4⟩ := levLin E a U Ξ q
  have l2 := (levLin E a U Ξ q).2.1
  have sub_eq : ∀ {p : ℕ} (x y : Co Ξ p), x - y = (1 : ℂ) • x + (-1 : ℂ) • y := fun x y => by
    refine AlternatingMap.ext fun X => ?_
    change x X - y X = (1 : ℂ) • x X + (-1 : ℂ) • y X
    rw [one_smul, neg_one_smul, sub_eq_add_neg]
  have lsub : ∀ x y : Co Ξ q, IsLev U Ξ x → IsLev U Ξ y → IsLev U Ξ (x - y) := fun x y hx hy => by
    rw [sub_eq]; exact l1 x y _ _ hx hy
  have dsub : ∀ x y : Co Ξ q, dCo (smLie Ξ) x = 0 → dCo (smLie Ξ) y = 0 → dCo (smLie Ξ) (x - y) = 0 := fun x y hx hy => by
    rw [sub_eq, l2, hx, hy, smul_zero, smul_zero, add_zero]
  have hV : Val N α := fun X i => by
    obtain ⟨p1, p2, p3⟩ := l3 α hα X i
    obtain ⟨R, hR'⟩ := hs
    refine hN.cpt _ p1 (hasLev_of hUo p2) (p3 r hr) ⟨R, fun g hg => ?_⟩
    rw [Pf.cmp_ev, hR' X g hg]; rfl
  have key : ∀ T, IsOp N T → IsLev U Ξ (app T α) ∧ Val N (app T α) ∧ Val (sqSub E a r) (app T α) ∧
      dCo (smLie Ξ) (app T α) = 0 := fun T hT => by
    obtain ⟨p1, p2, p3, p4⟩ := appFacts E a U Ξ r hr N hN T hT q α hα hV
    exact ⟨p1, p2, p3, by rw [p4, hd, app_zero']⟩
  obtain ⟨h1, h2, h3, h4⟩ := key P hR.opP
  refine ⟨app P α, h1, h4, (resExact E a ha n e he U Ξ r c hc q _ h1 h4).2 h3 (co_ext fun X i => ?_), h3,
    fun X i => hN.grow _ (h2 X i), ?_⟩
  · rw [l4, l4, hR.ker _ (hV X i), AlternatingMap.zero_apply, map_zero]
  · refine exactLim E a ha U hUc Ξ q _ (fun k => app (Q k) α - app P α) (lsub _ _ hα h1) (dsub _ _ hd h4)
      (fun k => lsub _ _ (key _ (hR.opQ k)).1 h1) (fun k => dsub _ _ (key _ (hR.opQ k)).2.2.2 h4) (fun X i => ?_) fun k => ?_
    · have := locLim_sub (hR.lim _ (hV X i))
      simpa only [AlternatingMap.sub_apply, map_sub, l4] using this
    · obtain ⟨s1, -, -, s4⟩ := key _ (hR.opS k)
      have e1 : α - app P α - (app (Q k) α - app P α) = app (casA r c e) (app (S k) α) := by
        rw [sub_sub_sub_cancel_right]
        refine co_ext fun X i => ?_
        rw [AlternatingMap.sub_apply, map_sub, l4, l4, l4, hR.res k _ (hV X i)]
      rw [e1]
      exact (resExact E a ha n e he U Ξ r c hc q _ s1 s4).1
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.autOf :
    UpperTheory.V.Cj.H.AutOf := by
  intro E _ _ _ a U hU Ξ m q ω hω X i hc hg
  have hl := (UpperTheory.V.Cj.H.levLin E a U Ξ q).2.2.1 ω hω X i
  obtain ⟨W, _, _, _, ρ, -, hρ⟩ := UpperTheory.V.Cj.H.kType E a Ξ q
  obtain ⟨T, w, hT, hw⟩ := hρ ω hω.equiv X i
  generalize cmp i (ω X) = φ at hc hg hl hw ⊢
  refine ⟨hl.1, ?_, ?_, ?_, hg⟩
  · exact Subgroup.isOpen_mono (H₁ := U)
      (H₂ := { carrier := {k | finRep E a k φ = φ}
               one_mem' := by simp
               mul_mem' := fun {x y} hx hy => by
                 rw [Set.mem_setOf_eq] at hx hy ⊢
                 rw [map_mul, Module.End.mul_apply, hy, hx]
               inv_mem' := fun {x} hx => by
                 rw [Set.mem_setOf_eq] at hx ⊢
                 conv_lhs => rw [← hx]
                 rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] })
      (fun u hu => hl.2.1 u hu) hU
  · refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨ρ k w, by rw [hT, hw]⟩
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have key : ∃ c : ℂ, z φ = c • φ := by
      induction hz using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨t, u, rfl⟩ := hx
        exact ⟨_, hc t u⟩
      | algebraMap c => exact ⟨c, rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, hx⟩ := hx
        obtain ⟨d, hy⟩ := hy
        exact ⟨c + d, by rw [LinearMap.add_apply, hx, hy, add_smul]⟩
      | mul x y _ _ hx hy =>
        obtain ⟨c, hx⟩ := hx
        obtain ⟨d, hy⟩ := hy
        exact ⟨d * c, by rw [Module.End.mul_apply, hy, map_smul, hx, mul_smul]⟩
    obtain ⟨c, h⟩ := key
    exact Submodule.mem_span_singleton.2 ⟨c, h.symm⟩
end

section
theorem UpperTheory.V.Cj.partH : UpperTheory.V.Cj.PartH :=
  UpperTheory.V.Cj.H.partH_of UpperTheory.V.Cj.exactSub UpperTheory.V.Lit.Bor.frameEx UpperTheory.V.Lit.Bor.oneReal UpperTheory.V.Cj.H.harmSub
    UpperTheory.V.Cj.H.harmSS UpperTheory.V.Cj.H.hodgeEx UpperTheory.V.Cj.H.charOf UpperTheory.V.Cj.H.autOf
end
