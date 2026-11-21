import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients

section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SatInd
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Abstract

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem idem_map {π : Representation ℂ G V} {π' : Representation ℂ G W} (hπ : IsSmooth π) (hπ' : IsSmooth π')
    {H : Subgroup G} (hH : IsCompact (H : Set G)) (f : V →ₗ[ℂ] W) (hf : ∀ g v, f (π g v) = π' g (f v)) (v : V) :
    f (idem hπ hH v) = idem hπ' hH (f v) := by
  have hy : f (idem hπ hH v) ∈ fixed π' H := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← hf, GlobalTheory.LGrp.mem_fixed.1 (idem_mem hπ hH v) k hk]
  have hk : v - idem hπ hH v ∈ twKer π H 1 := (idem_eq_zero_iff hπ hH).1 (by
    rw [map_sub, idem_of_mem hπ hH (idem_mem hπ hH v), sub_self])
  have hle : twKer π H 1 ≤ (twKer π' H 1).comap f := Submodule.span_le.2 (by
    rintro _ ⟨u, z, rfl⟩
    exact Submodule.subset_span ⟨u, f z, by rw [map_sub, map_smul, hf]⟩)
  have h0 : idem hπ' hH (f (v - idem hπ hH v)) = 0 := (idem_eq_zero_iff hπ' hH).2 (hle hk)
  rw [map_sub, map_sub, idem_of_mem hπ' hH hy, sub_eq_zero] at h0
  exact h0.symm

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, TopologicalSpace (Γ a)]
  [∀ a, IsTopologicalGroup (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  {ρ : ∀ a, Representation ℂ (Γ a) (X a)} {U : ∀ a, Subgroup (Γ a)}

theorem idem_tprod (hs : ∀ a, IsSmooth (ρ a)) (hc : ∀ a, IsCompact (U a : Set (Γ a)))
    (hC : IsCompact (Subgroup.pi Set.univ U : Set (∀ a, Γ a))) (x : ∀ a, X a) :
    idem (isSmooth_piTensor hs) hC (PiTensorProduct.tprod ℂ x) = PiTensorProduct.tprod ℂ fun a => idem (hs a) (hc a) (x a) := by
  classical
  have hS := isSmooth_piTensor hs
  have h1 : ∀ (x : ∀ a, X a) (i : α) (y : X i),
      idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i (idem (hs i) (hc i) y))) =
        idem hS hC (PiTensorProduct.tprod ℂ (Function.update x i y)) := fun x i y => by
    let l : X i →ₗ[ℂ] ⨂[ℂ] a, X a := idem hS hC ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap x i
    have hk : twKer (ρ i) (U i) 1 ≤ LinearMap.ker l := Submodule.span_le.2 (by
      rintro _ ⟨u, z, rfl⟩
      show l _ = 0
      rw [map_sub, MonoidHom.one_apply, Units.val_one, one_smul, sub_eq_zero]
      have hu : Pi.mulSingle i (u : Γ i) ∈ Subgroup.pi Set.univ U := fun a _ => by
        show (Pi.mulSingle i (u : Γ i) : ∀ a, Γ a) a ∈ U a
        by_cases e : a = i
        · subst e; simp
        · rw [Pi.mulSingle_eq_of_ne e]; exact one_mem _
      refine Eq.trans ?_ (idem_apply_mem hS hC hu (PiTensorProduct.tprod ℂ (Function.update x i z)))
      rw [piTensor_tprod]
      show idem hS hC (PiTensorProduct.tprod ℂ _) = _
      congr 2
      funext a
      by_cases e : a = i
      · subst e; simp
      · simp [e])
    have h2 : l (idem (hs i) (hc i) y - y) = 0 := hk ((idem_eq_zero_iff (hs i) (hc i)).1 (by
      rw [map_sub, idem_of_mem _ _ (idem_mem _ _ _), sub_self]))
    rwa [map_sub, sub_eq_zero] at h2
  have h2 : ∀ (x : ∀ a, X a) (s : Finset α),
      idem hS hC (PiTensorProduct.tprod ℂ (s.piecewise (fun a => idem (hs a) (hc a) (x a)) x)) =
        idem hS hC (PiTensorProduct.tprod ℂ x) := fun x s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.piecewise_insert, h1, ← ih, ← Finset.piecewise_eq_of_notMem s (fun a => idem (hs a) (hc a) (x a)) x hi,
        Function.update_eq_self]
  rw [← h2 x Finset.univ, Finset.piecewise_univ, idem_of_mem]
  refine GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_
  rw [piTensor_tprod]
  congr 1
  funext a
  exact GlobalTheory.LGrp.mem_fixed.1 (idem_mem _ _ _) _ (hg a trivial)

end Abstract

section Completion

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSatVecGL_twist {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {x : V} {B : Multiset ℂˣ}
    (hx : IsSatVecGL w ρ x B) (s : ℂ) {z : ℂˣ} (hz : (z : ℂ) = (qV E w : ℂ) ^ (-s)) :
    IsSatVecGL w (twist ρ (detChar (Fin n) (absPow (w.adicCompletion E) s))) x (B.map (· * z)) := by
  have hfix : x ∈ fixed (twist ρ (detChar (Fin n) (absPow (w.adicCompletion E) s))) (KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun g hg => by
      rw [twist_apply, detChar_apply, absPow_det_of_mem s hg, Units.val_one, one_smul]
      exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 g hg
  refine ⟨hx.1, hfix, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
  rw [GlobalTheory.SphGal.satEig_map_mul, mul_smul, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec, smul_finsum]
  refine finsum_congr fun c => ?_
  by_cases hc : Tj ℂ n (Ov E w) ϖ j c.out = 0
  · simp [hc]
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hc
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have e2 : Matrix.GeneralLinearGroup.det c.out =
      Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ hϖ0 ^ j * Matrix.GeneralLinearGroup.det b := by
    apply Units.ext
    change c.out.val.det = a.val.det * _ * b.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, GlobalTheory.SphGal.det_diagJ ϖ hj]
    simp
  have e3 : absPow (w.adicCompletion E) s (Units.mk0 ϖ hϖ0) = z := Units.ext (by
    have : ordV E w ϖ = 1 := by
      rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v ϖ = _ from hϖ]; rfl
    rw [val_absPow_completion, hz, Units.val_mk0, this]
    simp)
  rw [twist_apply, detChar_apply, e2, map_mul, map_mul, absPow_det_of_mem s ha, absPow_det_of_mem s hb, map_pow, e3,
    one_mul, mul_one, smul_comm, Units.val_pow_eq_pow_val]

variable {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)

theorem isSatVecGL_multiProd {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    {π : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a)} (hs : ∀ a, IsSmooth (π a))
    {S : Fin c → Multiset ℂˣ} {x : ∀ a, X a} (hx : ∀ a, IsSatVecGL w (π a) (x a) (S a))
    {f : IndSp (stdBlocks N h) (piTensor π)} (hf : f ∈ fixed (multiProd (stdBlocks N h) π) (KGL w n)) (h0 : f ≠ 0)
    {r : ℂ} (hr : f.1.1 1 = r • PiTensorProduct.tprod ℂ x) :
    IsSatVecGL w (multiProd (stdBlocks N h) π) f (∑ a, S a) := by
  have hKO : ∀ m, KGL w m = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  have hf' := hf
  rw [hKO] at hf'
  choose Z iZ mZ R β l y hR hβ hyS h1 hl using fun a => exists_model (w := w) (hx a).2.2.1
  have hy : ∀ a, y a ∈ fixed (R a) (KO _ _) := fun a => hKO _ ▸ (hyS a).2.1
  obtain ⟨F, hF, hF1⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor R) (x := PiTensorProduct.tprod ℂ y)
    fun g hg => by
      rw [piTensor_tprod]
      congr 1
      exact funext fun a => GlobalTheory.LGrp.mem_fixed.1 (hy a) _ (hg a)
  obtain ⟨Y, hYe, hY⟩ := exists_map_isSatVecGL h h1 hl hF hF1
  rw [funext hβ] at hY
  refine ⟨h0, hf, hY.2.2.1, fun ϖ hϖ j hj => ?_⟩
  have hϖ0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ
  have hT := Tj_mem_hecke (n := n) hϖ j
  have hK : IsCommensurated (KGL w n) := Final.GLintComm E w n
  have e1 := (map_heckeVec (ρ := multiProd (stdBlocks N h) R) hK hT Y hYe F).trans (hY.2.2.2 ϖ hϖ j hj)
  rw [hKO] at hT hK e1 ⊢
  have hp : ∀ q : GL (Fin n) (w.adicCompletion E) ⧸ KO (w.adicCompletion E) (Fin n),
      ∃ p : parab (w.adicCompletion E) (stdBlocks N h), ((p : GL (Fin n) (w.adicCompletion E)) : _ ⧸ KO _ _) = q :=
    fun q => by
      obtain ⟨p, hp, u, hu, e⟩ := (LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).2.2.2.2.2.2.2.2 q.out
      exact ⟨⟨p, hp⟩, (QuotientGroup.eq.2 (by simpa [e] using hu)).trans q.out_eq'⟩
  choose p hp using hp
  have hω : ∀ q a, ∃ t : ℂ, Tj ℂ n (Ov E w) ϖ j (p q) ≠ 0 →
      idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (π a (leviProj _ _ (p q) a) (x a)) = t • x a ∧
      idem (hR a) GlobalTheory.SplitFlip.isCompact_KO (R a (leviProj _ _ (p q) a) (y a)) = t • y a := fun q a => by
    by_cases hq : Tj ℂ n (Ov E w) ϖ j (p q) = 0
    · exact ⟨0, fun e => absurd hq e⟩
    obtain ⟨i1, i2⟩ := intM_of_Tj hϖ0 hϖ hq
    obtain ⟨l, hl, e⟩ := dosetInd_eq_Tj hϖ0 hϖ (g := leviProj _ _ (p q) a) (fun s t => i1 _ _) fun s t => by
      have := i2 (stdBlocks N h ⟨a, s⟩) (stdBlocks N h ⟨a, t⟩)
      rw [← Pi.inv_apply, ← map_inv]
      rw [Units.val_mul, tor_val, Matrix.diagonal_mul] at this ⊢
      exact this
    exact ⟨_, fun _ => ⟨idem_of_isSatVecGL (hs a) (hx a) hϖ hl e, idem_of_isSatVecGL (hR a) (hyS a) hϖ hl e⟩⟩
  choose ω hω using hω
  rw [heckeVec_multiProd _ hK hT hR hF (hF1.trans (one_smul ℂ _).symm) p hp ω (fun q hq a => (hω q a hq).2),
    map_smul] at e1
  rw [heckeVec_multiProd _ hK hT hs hf' hr p hp ω (fun q hq a => (hω q a hq).1), smul_left_injective ℂ hY.1 e1]

end Completion

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SatInd
open scoped TensorProduct

namespace PositivityTheory.Rg.Rs.SatakeVectors.Core

section Tensor

variable {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]

def evT (ev : ∀ a, X a →ₗ[ℂ] ℂ) : (⨂[ℂ] a, X a) →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap ev)

theorem evT_tprod (ev : ∀ a, X a →ₗ[ℂ] ℂ) (x : ∀ a, X a) :
    evT ev (PiTensorProduct.tprod ℂ x) = ∏ a, ev a (x a) := by
  simp [evT]

theorem piTensor_twist (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (χ : ∀ a, Γ a →* ℂˣ) (g : ∀ a, Γ a)
    (y : ⨂[ℂ] a, X a) :
    piTensor (fun a => twist (ρ a) (χ a)) g y = ((∏ a, χ a (g a) : ℂˣ) : ℂ) • piTensor ρ g y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, piTensor_tprod, piTensor_tprod, smul_comm]
    congr 1
    simp only [twist_apply]
    rw [MultilinearMap.map_smul_univ, Units.coe_prod]
  | add y₁ y₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, smul_add]

end Tensor

section Completion

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
  {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
  {X : Fin c → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  {π : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a)}

omit h in

theorem evT_idem (hs : ∀ a, IsSmooth (π a))
    (hC : IsCompact (Subgroup.pi Set.univ (fun a => KO (w.adicCompletion E) (Fin (N a))) :
      Set (∀ a, GL (Fin (N a)) (w.adicCompletion E))))
    (ev : ∀ a, X a →ₗ[ℂ] ℂ) (v : ⨂[ℂ] a, X a)
    (hinv : ∀ (μ κ : ∀ a, GL (Fin (N a)) (w.adicCompletion E)), (∀ a, κ a ∈ KO (w.adicCompletion E) (Fin (N a))) →
      evT ev (piTensor π (μ * κ) v) = evT ev (piTensor π μ v))
    (μ : ∀ a, GL (Fin (N a)) (w.adicCompletion E)) :
    evT ev (piTensor π μ (idem (isSmooth_piTensor hs) hC v)) = evT ev (piTensor π μ v) := by
  let Φ : (⨂[ℂ] a, X a) →ₗ[ℂ] ((∀ a, GL (Fin (N a)) (w.adicCompletion E)) → ℂ) :=
    { toFun := fun y ν => evT ev (piTensor π ν y)
      map_add' := fun y y' => funext fun ν => by simp [map_add]
      map_smul' := fun r y => funext fun ν => by simp [map_smul] }
  have hΦs : ∀ y, Φ y ∈ smoothPart (rightReg ℂ (∀ a, GL (Fin (N a)) (w.adicCompletion E)) ℂ) := fun y =>
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((isSmooth_piTensor hs y).mem_nhds (by simp)) fun g hg =>
      funext fun ν => by
        have hg' : piTensor π g y = y := hg
        show evT ev (piTensor π (ν * g) y) = evT ev (piTensor π ν y)
        rw [map_mul, Module.End.mul_apply, hg'])
  let Φ' : (⨂[ℂ] a, X a) →ₗ[ℂ] smoothPart (rightReg ℂ (∀ a, GL (Fin (N a)) (w.adicCompletion E)) ℂ) :=
    Φ.codRestrict _ hΦs
  have hΦe : ∀ g y, Φ' (piTensor π g y) = smoothRep (rightReg ℂ _ ℂ) g (Φ' y) := fun g y =>
    Subtype.ext (funext fun ν => by
      show evT ev (piTensor π ν (piTensor π g y)) = evT ev (piTensor π (ν * g) y)
      rw [map_mul, Module.End.mul_apply])
  have key := idem_map (isSmooth_piTensor hs) (isSmooth_smoothRep _) hC Φ' hΦe v
  have hfix : Φ' v ∈ fixed (smoothRep (rightReg ℂ (∀ a, GL (Fin (N a)) (w.adicCompletion E)) ℂ))
      (Subgroup.pi Set.univ fun a => KO (w.adicCompletion E) (Fin (N a))) :=
    GlobalTheory.LGrp.mem_fixed.2 fun κ hκ => Subtype.ext (funext fun ν => by
      show evT ev (piTensor π (ν * κ) v) = evT ev (piTensor π ν v)
      exact hinv ν κ fun a => hκ a trivial)
  rw [idem_of_mem _ _ hfix] at key
  exact congrFun (congrArg Subtype.val key) μ

theorem isSatVecGL_of_levi (hs : ∀ a, IsSmooth (π a)) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ a, ∀ x ∈ fixed (π a) (KGL w (N a)), x ≠ 0 → IsSatVecGL w (π a) x (S a))
    (z : Fin c → ℂˣ) (hz : ∀ a, (z a : ℂ) = (qV E w : ℂ) ^ ((modExp (fun a => Fin (N a)) a : ℂ) / 2))
    (ev : ∀ a, X a →ₗ[ℂ] ℂ) (G : GL (Fin n) (w.adicCompletion E) → ℂ)
    (hGK : ∀ g, ∀ k ∈ KGL w n, G (g * k) = G g)
    (hGN : ∀ u ∈ unipRad (w.adicCompletion E) (stdBlocks N h), ∀ g, G (u * g) = G g)
    (v : ⨂[ℂ] a, X a)
    (hGv : ∀ μ : ∀ a, GL (Fin (N a)) (w.adicCompletion E),
      G (leviEmb (w.adicCompletion E) (stdBlocks N h) μ) = evT ev (piTensor π μ v))
    (hG0 : G ≠ 0) :
    IsSatVecGL w (rightReg ℂ _ ℂ) G (∑ a, (S a).map (· * z a)) := by
  classical
  have hKO : ∀ m, KGL w m = KO (w.adicCompletion E) (Fin m) := fun m => (SphCompletion.KO_completion w m).symm
  let χ : ∀ a, GL (Fin (N a)) (w.adicCompletion E) →* ℂˣ := fun a =>
    detChar (Fin (N a)) (absPow (w.adicCompletion E) (-((modExp (fun a => Fin (N a)) a : ℂ) / 2)))
  let π' : ∀ a, Representation ℂ (GL (Fin (N a)) (w.adicCompletion E)) (X a) := fun a => twist (π a) (χ a)
  have hs' : ∀ a, IsSmooth (π' a) := fun a =>
    isSmooth_twist (hs a) (isSmoothChar_of_isUnram (isUnram_absPow _ _)).detChar
  have hχK : ∀ a, ∀ g ∈ KO (w.adicCompletion E) (Fin (N a)), χ a g = 1 := fun a g hg =>
    absPow_det_of_mem _ (by rw [hKO]; exact hg)
  have hC : IsCompact (Subgroup.pi Set.univ (fun a => KO (w.adicCompletion E) (Fin (N a))) :
      Set (∀ a, GL (Fin (N a)) (w.adicCompletion E))) := isCompact_univ_pi fun a => GlobalTheory.SplitFlip.isCompact_KO
  have hsT := isSmooth_piTensor hs
  set P := idem hsT hC with hPdef
  have hPfix : ∀ y, ∀ g : ∀ a, GL (Fin (N a)) (w.adicCompletion E),
      (∀ a, g a ∈ KO (w.adicCompletion E) (Fin (N a))) → piTensor π' g (P y) = P y := fun y g hg => by
    rw [piTensor_twist, Finset.prod_eq_one fun a _ => hχK a _ (hg a), Units.val_one, one_smul]
    exact GlobalTheory.LGrp.mem_fixed.1 (idem_mem hsT hC y) g fun a _ => hg a
  set Bt := ∑ a, (S a).map (· * z a) with hBt
  have hQ : ∀ y, ∀ f : IndSp (stdBlocks N h) (piTensor π'),
      f ∈ fixed (multiProd (stdBlocks N h) π') (KGL w n) → f.1.1 1 = P y →
      (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (multiProd (stdBlocks N h) π') (KGL w n) (Tj ℂ n (Ov E w) ϖ j) f =
        satEig (qV E w) n Bt j • f) ∧ (f ≠ 0 → Bt.card = n) := by
    intro y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r x =>
      intro f hf hf1
      by_cases hf0 : f = 0
      · subst hf0
        refine ⟨fun ϖ hϖ j hj => ?_, fun h0 => absurd rfl h0⟩
        rw [smul_zero]
        exact (SatCompare.heckeLin (Final.GLintComm E w n) (Tj_mem_hecke hϖ j) _).map_zero
      have hfKO : f ∈ fixed (multiProd (stdBlocks N h) π') (KO (w.adicCompletion E) (Fin n)) := by
        rw [← hKO]; exact hf
      have e1 : f.1.1 1 = r • PiTensorProduct.tprod ℂ fun a => idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (x a) := by
        rw [hf1, map_smul, hPdef, idem_tprod hs (fun a => GlobalTheory.SplitFlip.isCompact_KO) hC]
      have hx0 : ∀ a, idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (x a) ≠ 0 := fun a ha => hf0 (by
        refine eq_zero_of_apply_one (stdBlocks N h) hfKO ?_
        rw [e1, MultilinearMap.map_coord_zero _ a ha, smul_zero])
      have hsat : ∀ a, IsSatVecGL w (π' a) (idem (hs a) GlobalTheory.SplitFlip.isCompact_KO (x a)) ((S a).map (· * z a)) :=
        fun a => isSatVecGL_twist (hS a _ (by rw [hKO]; exact idem_mem _ _ _) (hx0 a)) _ (by rw [hz a, neg_neg])
      have hf' := isSatVecGL_multiProd h hs' hsat hf hf0 e1
      exact ⟨hf'.2.2.2, fun _ => hf'.2.2.1⟩
    | add y₁ y₂ ih₁ ih₂ =>
      intro f hf hf1
      obtain ⟨f₁, hf₁, e₁⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor π') (x := P y₁) (hPfix y₁)
      obtain ⟨f₂, hf₂, e₂⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor π') (x := P y₂) (hPfix y₂)
      have hf₁' : f₁ ∈ fixed (multiProd (stdBlocks N h) π') (KGL w n) := by rw [hKO]; exact hf₁
      have hf₂' : f₂ ∈ fixed (multiProd (stdBlocks N h) π') (KGL w n) := by rw [hKO]; exact hf₂
      have hsum : f = f₁ + f₂ := by
        rw [← sub_eq_zero]
        refine eq_zero_of_apply_one (stdBlocks N h) (sub_mem (by rw [← hKO]; exact hf) (add_mem hf₁ hf₂)) ?_
        show f.1.1 1 - (f₁.1.1 1 + f₂.1.1 1) = 0
        rw [hf1, e₁, e₂, map_add, sub_self]
      obtain ⟨H₁, C₁⟩ := ih₁ f₁ hf₁' e₁
      obtain ⟨H₂, C₂⟩ := ih₂ f₂ hf₂' e₂
      refine ⟨fun ϖ hϖ j hj => ?_, fun h0 => ?_⟩
      · have := (SatCompare.heckeLin (Final.GLintComm E w n) (Tj_mem_hecke hϖ j)
          (multiProd (stdBlocks N h) π')).map_add f₁ f₂
        simp only [SatCompare.heckeLin_apply] at this
        rw [hsum, this, H₁ ϖ hϖ j hj, H₂ ϖ hϖ j hj, smul_add]
      · by_cases h1 : f₁ = 0
        · refine C₂ fun h2 => h0 ?_
          rw [hsum, h1, h2, add_zero]
        · exact C₁ h1
  obtain ⟨f, hf, hf1⟩ := exists_fixed_apply_one (stdBlocks N h) (ρ := piTensor π') (x := P v) (hPfix v)
  have hfK : f ∈ fixed (multiProd (stdBlocks N h) π') (KGL w n) := by rw [hKO]; exact hf
  let Y : IndSp (stdBlocks N h) (piTensor π') →ₗ[ℂ] (GL (Fin n) (w.adicCompletion E) → ℂ) :=
    (evT ev).compLeft _ ∘ₗ Submodule.subtype _ ∘ₗ Submodule.subtype _
  have hYe : ∀ g F, Y (multiProd (stdBlocks N h) π' g F) = rightReg ℂ _ ℂ g (Y F) := fun _ _ => rfl
  have hδ : ∀ μ : ∀ a, GL (Fin (N a)) (w.adicCompletion E),
      (deltaHalf (w.adicCompletion E) (fun a => Fin (N a)) μ : ℂ) * ((∏ a, χ a (μ a) : ℂˣ) : ℂ) = 1 := fun μ => by
    rw [← Units.val_mul, deltaHalf_apply, ← Finset.prod_mul_distrib, Finset.prod_eq_one, Units.val_one]
    intro a _
    simp only [χ, detChar_apply, absPow_neg, MonoidHom.inv_apply, mul_inv_cancel]
  have hinv : ∀ (μ κ : ∀ a, GL (Fin (N a)) (w.adicCompletion E)), (∀ a, κ a ∈ KO (w.adicCompletion E) (Fin (N a))) →
      evT ev (piTensor π (μ * κ) v) = evT ev (piTensor π μ v) := fun μ κ hκ => by
    rw [← hGv, ← hGv, map_mul, hGK]
    have := ((LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).1 κ 1 (one_mem _)).2 ⟨hκ, one_mem _⟩
    rw [mul_one] at this
    rw [hKO]; exact this
  have hYG : Y f = G := by
    funext g
    obtain ⟨p, hp, x, hx, rfl⟩ := (LeviInt.levi_integral_facts _ _ _ _ (stdBlocks N h)).2.2.2.2.2.2.2.2 g
    rw [hGK _ _ (by rw [hKO]; exact hx)]
    show evT ev (f.1.1 (p * x)) = _
    rw [apply_mul_of_fixed _ hf p hx]
    obtain ⟨u, hu, hpu⟩ := exists_levi_mul_unip _ (stdBlocks N h) ⟨p, hp⟩
    have hlaw := parInd_law (stdBlocks N h) (piTensor π') f ⟨p, hp⟩ 1
    rw [mul_one] at hlaw
    generalize leviProj (w.adicCompletion E) (stdBlocks N h) ⟨p, hp⟩ = μ at hpu hlaw
    have hN := leviEmb_mem_normalizer (w.adicCompletion E) (stdBlocks N h) μ
    have hu' := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
    have hG1 : G p = G (leviEmb (w.adicCompletion E) (stdBlocks N h) μ) := by
      have e : p = (leviEmb (w.adicCompletion E) (stdBlocks N h) μ * u *
          (leviEmb (w.adicCompletion E) (stdBlocks N h) μ)⁻¹) * leviEmb (w.adicCompletion E) (stdBlocks N h) μ := by
        rw [inv_mul_cancel_right]; exact hpu
      rw [e]
      exact hGN _ hu' _
    rw [hG1, hlaw, hf1, piTensor_twist, smul_smul, map_smul, smul_eq_mul, hδ, one_mul,
      evT_idem hs hC ev v hinv μ, hGv]
  have hfne : f ≠ 0 := fun e => hG0 (by rw [← hYG, e, map_zero])
  obtain ⟨hH, hcard⟩ := hQ v f hfK hf1
  refine ⟨hG0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext fun g => hGK g k hk, hcard hfne, fun ϖ hϖ j hj => ?_⟩
  rw [← hYG, ← map_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hϖ j) Y hYe f, hH ϖ hϖ j hj, map_smul]

end Completion

end PositivityTheory.Rg.Rs.SatakeVectors.Core

end
end
