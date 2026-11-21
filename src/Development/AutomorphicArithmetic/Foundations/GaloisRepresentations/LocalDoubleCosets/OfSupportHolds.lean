import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.CellStep
import GroundTheory.AutomorphicForms.GeometricLemmaFiltration
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.FunInv
import GroundTheory.AutomorphicForms.WhittakerCells
import GroundTheory.AutomorphicForms.Iwasawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.ExistsStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.EigZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.JacSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.LocDescOf

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.stabSub :
    StabSub := by
  intro H _ _ _ _ _ _ τ p hp hτ hper L hL
  obtain ⟨K, hKc, hKL⟩ := GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset
    (hL.mem_nhds L.one_mem)
  let L₀ : Subgroup H :=
    { carrier := {l | ∀ i < p, τ^[i] l ∈ K}
      one_mem' := fun i _ => by rw [iterate_map_one]; exact K.one_mem
      mul_mem' := fun ha hb i hi => by
        rw [iterate_map_mul]; exact K.mul_mem (ha i hi) (hb i hi)
      inv_mem' := fun ha i hi => by
        rw [iterate_map_inv]; exact K.inv_mem (ha i hi) }
  have hset : (L₀ : Set H) = ⋂ i ∈ {i : ℕ | i < p}, τ^[i] ⁻¹' (K : Set H) := by
    ext l; simp [L₀]
  have hopen : IsOpen (L₀ : Set H) := by
    rw [hset]
    exact (Set.finite_lt_nat p).isOpen_biInter
      (fun i _ => K.isOpen.preimage (hτ.iterate i))
  have hsub : (L₀ : Set H) ⊆ K := fun l hl => by
    have := hl 0 hp
    simpa using this
  refine ⟨L₀, hKc.of_isClosed_subset (L₀.isClosed_of_isOpen hopen) hsub, hopen,
    fun l hl => hKL (hsub hl), fun l => ?_⟩
  show (∀ i < p, τ^[i] (τ l) ∈ K) ↔ ∀ i < p, τ^[i] l ∈ K
  constructor
  · intro h i hi
    rcases i with _ | j
    · have h1 := h (p - 1) (by omega)
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper] at h1
      simpa using h1
    · rw [Function.iterate_succ_apply]
      exact h j (by omega)
  · intro h i hi
    rw [← Function.iterate_succ_apply]
    by_cases hlt : i + 1 < p
    · exact h (i + 1) hlt
    · have hip : i + 1 = p := by omega
      rw [Nat.succ_eq_add_one, hip, hper]
      simpa using h 0 hp
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.distZero :
    CellStep → DistZero := by
  intro hstep X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hcomm χ hχ k x hfix huniq hcl D hD hsum f hf
  obtain ⟨C, hC⟩ : ∃ C : Fin k → Set X, C = fun j => MulAction.orbit H (x j) := ⟨_, rfl⟩
  have hCl : ∀ l y, y ∈ C l ↔ y ∈ MulAction.orbit H (x l) := by
    intro l y
    rw [hC]
  have hcov : ∀ y, ∃ l, y ∈ C l := fun y => ⟨(huniq y).exists.choose, (hCl _ _).mpr (huniq y).exists.choose_spec⟩
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hi hj
    exact hij ((huniq y).unique ((hCl _ _).mp hi) ((hCl _ _).mp hj))
  have hcl' : ∀ j, closure (C j) ⊆ ⋃ l, ⋃ (_ : j ≤ l), C l := by
    rw [hC]
    exact hcl
  have hsorb : ∀ l y, y ∈ C l → s y ∈ C l := by
    intro l y hy
    rw [hCl] at hy ⊢
    obtain ⟨g, rfl⟩ := hy
    exact ⟨τ g, by rw [hcomm, hfix]⟩
  have key : ∀ j : ℕ, j ≤ k → ∀ g ∈ GroundTheory.Automorphic.Whittaker.supportedIn (GroundTheory.Automorphic.Parabolic.cellUnion C j), D g = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ g hg
      rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Parabolic.cellUnion_zero] at hg
      have hg0 : g = 0 := by
        funext y
        by_contra hy
        exact hg.2 hy
      rw [hg0, map_zero]
    | succ j ih =>
      intro hjk g hg
      have hj : j < k := by omega
      have hU : GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1) = GroundTheory.Automorphic.Parabolic.cellUnion C ((⟨j, hj⟩ : Fin k) : ℕ) ∪ C ⟨j, hj⟩ :=
        GroundTheory.Automorphic.Parabolic.cellUnion_succ (C := C) ⟨j, hj⟩
      refine hstep X H s τ p hp hs hτ hsp hτp hcomm χ hχ D hD hsum
        (GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1)) (closure (C ⟨j, hj⟩)) (x ⟨j, hj⟩)
        (GroundTheory.Automorphic.Parabolic.isOpen_cellUnion hdisj hcov hcl' (j + 1)) isClosed_closure ?_ ?_ ?_ (hfix _) ?_ g hg
      · rw [Set.inter_comm]
        have h1 := GroundTheory.Automorphic.Parabolic.closure_inter_cellUnion_succ hdisj hcl' ⟨j, hj⟩
        rw [h1, hC]
      · intro h y hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hy ⊢
        obtain ⟨l, hl, hyl⟩ := hy
        refine ⟨l, hl, ?_⟩
        rw [hCl] at hyl ⊢
        obtain ⟨g', rfl⟩ := hyl
        exact ⟨h * g', mul_smul _ _ _⟩
      · intro y
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion, GroundTheory.Automorphic.Parabolic.mem_cellUnion]
        constructor
        · rintro ⟨l, hl, hsy⟩
          obtain ⟨m, hm⟩ := hcov y
          have hlm : l = m := (huniq (s y)).unique ((hCl _ _).mp hsy) ((hCl _ _).mp (hsorb m y hm))
          subst hlm
          exact ⟨l, hl, hm⟩
        · rintro ⟨l, hl, hy⟩
          exact ⟨l, hl, hsorb l y hy⟩
      · intro g' hg'
        rw [Submodule.mem_inf, GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Whittaker.mem_vanishingOn] at hg'
        obtain ⟨hg1, hg2⟩ := hg'
        apply ih (by omega)
        rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn]
        refine ⟨hg1.1, ?_⟩
        intro y hy
        have hyU := hg1.2 hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hyU ⊢
        obtain ⟨l, hl, hyl⟩ := hyU
        refine ⟨l, ?_, hyl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
        · exact hlt
        · exfalso
          apply hy
          apply hg2
          have hleq : l = ⟨j, hj⟩ := Fin.ext heq
          rw [hleq] at hyl
          exact subset_closure hyl
  apply key k le_rfl f
  rw [GroundTheory.Automorphic.Parabolic.cellUnion_of_cover hcov, GroundTheory.Automorphic.Whittaker.mem_supportedIn]
  exact ⟨hf, Set.subset_univ _⟩
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

private theorem comp_mem_Cc {X : Type} [TopologicalSpace X] (s : X → X) (q : ℕ) (hs : Continuous s)
    (hsp : ∀ x, s^[q + 1] x = x) {f : X → ℂ} (hf : f ∈ Cc X) : f ∘ s ∈ Cc X := by
  obtain ⟨h1, h2⟩ := hf
  let e : X ≃ₜ X :=
    { toFun := s
      invFun := s^[q]
      left_inv := fun y => by
        show s^[q] (s y) = y
        rw [← Function.iterate_succ_apply s q y, hsp]
      right_inv := fun y => by
        show s (s^[q] y) = y
        rw [← Function.iterate_succ_apply' s q y, hsp]
      continuous_toFun := hs
      continuous_invFun := hs.iterate q }
  exact ⟨h1.comp_continuous hs, h2.comp_homeomorph e⟩

theorem UpperTheory.Gal.LocD.distInv :
    DistZero → DistInv := by
  intro hZ X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL hχτ k x hxs horb hcl D hD f hf
  have hsp' : ∀ y, s^[p - 1 + 1] y = y := fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y
  have cc : ∀ g ∈ Cc X, g ∘ s ∈ Cc X := fun g hg => comp_mem_Cc s (p - 1) hs hsp' hg
  let D' : (X → ℂ) →ₗ[ℂ] ℂ := D.comp (LinearMap.funLeft ℂ ℂ s) - D
  have hD'apply : ∀ g, D' g = D (g ∘ s) - D g := fun g => rfl
  have key := hZ X H s τ p hp hs hτ hsp hτp hsτ χ hχL k x hxs horb hcl D' ?_ ?_ f hf
  · rw [hD'apply, sub_eq_zero] at key
    exact key
  · intro h g hg
    rw [hD'apply, hD'apply]
    set h' := τ^[p - 1] h with hh'
    have hτh : τ h' = h := by
      rw [hh', ← Function.iterate_succ_apply' τ (p - 1) h, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hp, hτp]
    have hχh : χ h' = χ h := by rw [← hχτ h', hτh]
    have hcomp : GroundTheory.Automorphic.Whittaker.transl h g ∘ s
        = GroundTheory.Automorphic.Whittaker.transl h' (g ∘ s) := by
      ext y
      simp only [Function.comp_apply, GroundTheory.Automorphic.Whittaker.transl_apply]
      rw [hsτ, map_inv, hτh]
    rw [hcomp, hD h' _ (cc g hg), hD h g hg, hχh]
    ring
  · intro g hg
    have h1 : ∀ i, D' (g ∘ s^[i]) = D (g ∘ s^[i + 1]) - D (g ∘ s^[i]) := fun i => rfl
    simp only [h1]
    rw [Finset.sum_range_sub (fun i => D (g ∘ s^[i]))]
    have hid : s^[p] = id := funext hsp
    simp [hid]
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

private theorem mem_Cc_mul_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {f : G → ℂ} (hf : f ∈ Cc G) (u : G) : (fun x => f (x * u)) ∈ Cc G := by
  rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
  refine ⟨hf.1.comp_continuous (continuous_mul_right u), ?_⟩
  exact hf.2.comp_homeomorph (Homeomorph.mulRight u)

@[reducible] private def act {G : Type} [Group G] (B N : Subgroup G) : MulAction (B × N) G where
  smul h g := (h.1 : G) * g * (h.2 : G)⁻¹
  one_smul g := by
    show ((1 : B × N).1 : G) * g * ((1 : B × N).2 : G)⁻¹ = g
    simp
  mul_smul h k g := by
    show ((h * k).1 : G) * g * ((h * k).2 : G)⁻¹ =
      (h.1 : G) * ((k.1 : G) * g * (k.2 : G)⁻¹) * (h.2 : G)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, _root_.mul_inv_rev]
    group

private theorem orbit_act {G : Type} [Group G] (B N : Subgroup G) (w : G) :
    letI := act B N; orbit (B × N) w = cell B N w := by
  letI := act B N
  show orbit (B × N) w = cell B N w
  ext g
  constructor
  · rintro ⟨⟨b, u⟩, rfl⟩
    exact ⟨b, b.2, (u : G)⁻¹, N.inv_mem u.2, rfl⟩
  · rintro ⟨b, hb, u, hu, rfl⟩
    refine ⟨(⟨b, hb⟩, ⟨u, hu⟩⁻¹), ?_⟩
    show b * w * (((⟨u, hu⟩⁻¹ : N) : G))⁻¹ = b * w * u
    simp

theorem UpperTheory.Gal.LocD.biInv :
    DistInv → BiInv := by
  intro hD G _ _ _ _ _ _ _ B N hB hN s p hp hs hsp hsB hsN hC η θ hη hθ hηs hθs D hDB hDN f hf
  obtain ⟨L, hLo, hL⟩ := hη
  obtain ⟨k, w, hw1, hw2, hw3⟩ := hC
  letI := act B N
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  haveI : LocallyCompactSpace N := hN.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (B × N) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : ContinuousSMul (B × N) G := ⟨by
    show Continuous fun q : (B × N) × G => (q.1.1 : G) * q.2 * (q.1.2 : G)⁻¹
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul continuous_snd).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv⟩
  let sB : B →* B := (s.comp B.subtype).codRestrict B (fun b => hsB b b.2)
  let sN : N →* N := (s.comp N.subtype).codRestrict N (fun u => hsN u u.2)
  let τ : B × N →* B × N := sB.prodMap sN
  have hτc : Continuous τ := by
    rw [MonoidHom.coe_prodMap]
    exact (Continuous.subtype_mk (hs.comp continuous_subtype_val) _).prodMap
      (Continuous.subtype_mk (hs.comp continuous_subtype_val) _)
  have hit : ∀ n (h : B × N), ((τ^[n] h).1 : G) = s^[n] h.1 ∧ ((τ^[n] h).2 : G) = s^[n] h.2 := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      simp only [Function.iterate_succ_apply']
      exact ⟨by rw [← (ih h).1]; rfl, by rw [← (ih h).2]; rfl⟩
  let χ : B × N →* ℂ := (η.comp (MonoidHom.fst B N)) * ((Units.coeHom ℂ).comp (θ.comp (MonoidHom.snd B N)))
  have hχ : ∀ h : B × N, χ h = η h.1 * (θ h.2 : ℂ) := fun h => rfl
  refine hD G (B × N) s τ p hp hs hτc hsp ?_ ?_ χ ?_ ?_ k w hw1 ?_ ?_ D ?_ f hf
  · intro h
    have := hit p h
    exact Prod.ext (Subtype.ext (this.1.trans (hsp _))) (Subtype.ext (this.2.trans (hsp _)))
  · intro h x
    show s ((h.1 : G) * x * (h.2 : G)⁻¹) = s h.1 * s x * (s h.2)⁻¹
    simp [map_mul, map_inv]
  · refine ⟨(L.comap B.subtype).prod θ.ker, ?_, ?_⟩
    · rw [Subgroup.coe_prod]
      exact (hLo.preimage continuous_subtype_val).prod hθ
    · intro l hl
      rw [Subgroup.mem_prod] at hl
      rw [hχ, hL l.1 hl.1, MonoidHom.mem_ker.1 hl.2]
      simp
  · intro h
    rw [hχ, hχ, hηs h.1 (τ h).1 rfl, hθs h.2 (τ h).2 rfl]
  · intro y
    simpa only [orbit_act] using hw2 y
  · intro j
    simpa only [orbit_act] using hw3 j
  · intro h g hg
    have hg' : (fun x => g (x * (h.2 : G))) ∈ Cc G := mem_Cc_mul_right hg _
    have e : GroundTheory.Automorphic.Whittaker.transl h g = fun x => (fun y => g (y * (h.2 : G))) ((h.1 : G)⁻¹ * x) := by
      funext x
      show g (((h⁻¹).1 : G) * x * ((h⁻¹).2 : G)⁻¹) = g ((h.1 : G)⁻¹ * x * h.2)
      simp
    rw [e, hDB h.1 _ hg', hDN h.2 g hg, hχ, mul_assoc]
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.prMem :
    PrMem := by
  intro G _ _ _ _ _ _ _ B hB _ _ μ _ χ hker
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  have hχc : Continuous (fun x : B => (χ x : ℂ)) := by
    have := continuous_of_continuousAt_one ((Units.coeHom ℂ).comp χ) ?_
    · exact this
    · refine (continuousAt_const (y := (1 : ℂ))).congr ?_
      filter_upwards [hker.mem_nhds (one_mem χ.ker)] with x hx
      have hx' : χ x = 1 := MonoidHom.mem_ker.mp hx
      simp [hx']
  have hint : ∀ f ∈ Cc G, ∀ g : G,
      Integrable (fun x : B => (χ x : ℂ) * f ((x : G)⁻¹ * g)) μ := by
    intro f hf g
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf
    obtain ⟨hlc, hcs⟩ := hf
    have hemb : Topology.IsClosedEmbedding (fun x : B => (x : G)⁻¹ * g) :=
      ((Homeomorph.inv G).trans (Homeomorph.mulRight g)).isClosedEmbedding.comp
        hB.isClosedEmbedding_subtypeVal
    have hcs' : HasCompactSupport (fun x : B => f ((x : G)⁻¹ * g)) :=
      hcs.comp_isClosedEmbedding hemb
    exact Continuous.integrable_of_hasCompactSupport
      (hχc.mul (hlc.continuous.comp hemb.continuous)) hcs'.mul_left
  refine ⟨fun f hf => ?_, fun f hf f' hf' => ?_⟩
  · rw [mem_indF]
    constructor
    · intro b g
      simp only [pr]
      rw [← integral_mul_left_eq_self _ b, ← integral_const_mul]
      congr 1
      ext x
      simp only [map_mul, Units.val_mul, Subgroup.coe_mul, _root_.mul_inv_rev, mul_assoc,
        inv_mul_cancel_left]
    · obtain ⟨K, -, hK⟩ := GroundTheory.Automorphic.exists_forall_mul_right hf
      refine ⟨(K : Subgroup G), K.isOpen, fun k hk g => ?_⟩
      simp only [pr]
      congr 1
      ext x
      rw [← mul_assoc, hK _ _ hk]
  · funext g
    simp only [pr, Pi.add_apply, mul_add]
    exact integral_add (hint f hf g) (hint f' hf' g)
end

section
noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace UpperTheory.Gal.LocD

theorem prLeft : PrLeft := by
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ b
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨c', hc'⟩ : ∃ c' : NNReal, map (· * b) μ = c' • μ :=
    ⟨_, isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨(((χ b)⁻¹ : ℂˣ) : ℂ) * ((c' : ℝ) : ℂ), fun f g => ?_⟩
  set H : B → ℂ := fun y => (χ y : ℂ) * f ((y : G)⁻¹ * g) with hH
  have key : pr B μ χ (fun x => f ((b : G)⁻¹ * x)) g
      = (((χ b)⁻¹ : ℂˣ) : ℂ) * ∫ x, H (x * b) ∂μ := by
    unfold pr
    rw [← integral_const_mul]
    congr 1
    ext x
    simp only [hH, map_mul, Units.val_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
    rw [Units.val_inv_eq_inv_val]
    field_simp [(χ b).ne_zero]
  have e := (MeasurableEquiv.mulRight b).measurableEmbedding.integral_map (μ := μ) H
  rw [MeasurableEquiv.coe_mulRight] at e
  rw [key, ← e, hc', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have : pr B μ χ f g = ∫ x, H x ∂μ := rfl
  rw [this]
  ring

end UpperTheory.Gal.LocD

end
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.prAuto :
    PrAuto := by
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ s p hp hs hper hsB hχ
  have hit : ∀ n (b : G), b ∈ B → s^[n] b ∈ B := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      rw [Function.iterate_succ_apply']
      exact hsB _ (ih b hb)
  have hleft : ∀ g, s^[p - 1] (s g) = g := by
    intro g
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact hper g
  have hright : ∀ g, s (s^[p - 1] g) = g := by
    intro g
    rw [← Function.iterate_succ_apply' s, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact hper g
  let σ : B ≃ₜ* B :=
    { toFun := fun b => ⟨s b, hsB _ b.2⟩
      invFun := fun b => ⟨s^[p - 1] b, hit _ _ b.2⟩
      left_inv := fun b => Subtype.ext (hleft b)
      right_inv := fun b => Subtype.ext (hright b)
      map_mul' := fun a b => Subtype.ext (map_mul s (a : G) (b : G))
      continuous_toFun := (hs.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((hs.iterate _).comp continuous_subtype_val).subtype_mk _ }
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B :=
    inferInstanceAs (SecondCountableTopology {x // x ∈ (B : Set G)})
  haveI hν : (Measure.map σ μ).IsHaarMeasure := σ.isHaarMeasure_map μ
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map σ μ) μ
  refine ⟨Measure.haarScalarFactor (Measure.map σ μ) μ,
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, fun f g => ?_⟩
  have hint : ∀ b : B, (χ b : ℂ) * (f ∘ s) ((b : G)⁻¹ * g) =
      (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) := by
    intro b
    rw [hχ b (σ b) rfl]
    simp [σ, map_mul, map_inv]
  have hm : ∫ c, (χ c : ℂ) * f ((c : G)⁻¹ * s g) ∂(Measure.map σ μ) =
      ∫ b, (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) ∂μ :=
    integral_map_equiv σ.toHomeomorph.toMeasurableEquiv (fun c : B => (χ c : ℂ) * f ((c : G)⁻¹ * s g))
  unfold pr
  simp_rw [hint]
  rw [← hm]
  conv_lhs => rw [heq]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
end

section
noncomputable section

open MeasureTheory

namespace UpperTheory.Gal.LocD

theorem prSurj : PrSurj := by
  classical
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ K hKo hKc hBK φ hφ
  obtain ⟨hφB, K0, hK0o, hφK0⟩ := mem_indF.1 hφ
  set S : Set B := {b | (b : G) ∈ K} with hS
  have hSo : IsOpen S := hKo.preimage continuous_subtype_val
  have hSc : IsCompact S := (hB.isClosedEmbedding_subtypeVal).isCompact_preimage hKc
  have hSpos : 0 < μ S := hSo.measure_pos μ ⟨1, K.one_mem⟩
  have hSfin : μ S < ⊤ := hSc.measure_lt_top
  have hr : (μ S).toReal ≠ 0 := (ENNReal.toReal_pos hSpos.ne' hSfin.ne).ne'
  have hr' : ((μ S).toReal : ℂ) ≠ 0 := by exact_mod_cast hr
  set c : ℂ := ((μ S).toReal : ℂ)⁻¹ with hc
  refine ⟨fun g => if g ∈ K then c * φ g else 0, ?_, ?_⟩
  · let K' : OpenSubgroup G := ⟨K ⊓ K0, hKo.inter hK0o⟩
    apply GroundTheory.Automorphic.mem_locallyConstantCompactSupport_of_forall_mul_right (R := ℂ) K'
    · exact HasCompactSupport.intro hKc (fun g hg => if_neg hg)
    · intro g k hk
      have hk' : k ∈ K ∧ k ∈ K0 := Subgroup.mem_inf.1 hk
      simp only [K.mul_mem_cancel_right hk'.1, hφK0 k hk'.2 g]
  · funext g
    obtain ⟨b0, hb0, k0, hk0, rfl⟩ := hBK g
    set b0' : B := ⟨b0, hb0⟩
    have key : ∀ b : B, ((b : G)⁻¹ * (b0 * k0) ∈ K) ↔ b ∈ (fun x => b0'⁻¹ * x) ⁻¹' S := by
      intro b
      simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv, b0']
      rw [← mul_assoc, K.mul_mem_cancel_right hk0, ← K.inv_mem_iff]
      simp [mul_inv_rev]
    have hTm : MeasurableSet ((fun x : B => b0'⁻¹ * x) ⁻¹' S) :=
      (hSo.preimage (continuous_const.mul continuous_id)).measurableSet
    have hint : (fun b : B => (χ b : ℂ) * (if ((b:G)⁻¹ * (b0 * k0)) ∈ K then c * φ ((b:G)⁻¹ * (b0*k0)) else 0))
        = ((fun x : B => b0'⁻¹ * x) ⁻¹' S).indicator (fun _ => c * φ (b0 * k0)) := by
      funext b
      by_cases h : ((b:G)⁻¹ * (b0 * k0)) ∈ K
      · rw [if_pos h, Set.indicator_of_mem ((key b).1 h)]
        have h1 := hφB b⁻¹ (b0 * k0)
        rw [Subgroup.coe_inv] at h1
        rw [h1]
        have hu : (χ b : ℂ) * (χ b⁻¹ : ℂ) = 1 := by
          rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
        linear_combination (c * φ (b0 * k0)) * hu
      · rw [if_neg h, Set.indicator_of_notMem (fun h' => h ((key b).2 h')), mul_zero]
    simp only [pr]
    rw [hint, integral_indicator_const _ hTm, measureReal_def, measure_preimage_mul]
    rw [hc, Complex.real_smul]
    field_simp

end UpperTheory.Gal.LocD

end
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.etaEx :
    EtaEx := by
  intro G _ _ _ _ _ _ B s p hp hper P κ hκ hs hB hne
  obtain ⟨f₀, hf₀, g₀, h0⟩ := hne
  obtain ⟨K, hK, hKf⟩ := GroundTheory.Automorphic.exists_forall_mul_left (R := ℂ) hf₀
  set e : B → ℂ := fun b => P (fun x => f₀ ((b : G)⁻¹ * x)) g₀ / P f₀ g₀ with he
  have hη : ∀ (b : B) (f : G → ℂ) (g : G), P (fun x => f ((b : G)⁻¹ * x)) g = e b * P f g := by
    intro b f g
    obtain ⟨c, hc⟩ := hB b
    have hc0 := hc f₀ g₀
    have : e b = c := by
      rw [he]; dsimp only; rw [hc0, mul_div_assoc, div_self h0, mul_one]
    rw [this, hc]
  have hpow : ∀ (n : ℕ) (f : G → ℂ) (g : G), P (f ∘ s^[n]) g = (κ : ℂ) ^ n * P f (s^[n] g) := by
    intro n
    induction n with
    | zero => intro f g; simp
    | succ n ih =>
      intro f g
      rw [Function.iterate_succ, ← Function.comp_assoc, hs, ih, Function.comp_apply, pow_succ]
      ring
  have hper' : s^[p] = id := funext hper
  have hκ1 : κ = 1 := by
    have h1 := hpow p f₀ g₀
    rw [hper', Function.comp_id, id] at h1
    have hk : (κ : ℂ) ^ p = 1 := by
      have := mul_right_cancel₀ h0 (h1.symm.trans (one_mul _).symm)
      exact this
    have hk' : κ ^ p = 1 := by exact_mod_cast hk
    exact (pow_eq_one_iff_of_nonneg hκ.le hp.ne').1 hk'
  have e1 : e 1 = 1 := by
    rw [he]; dsimp only; simp [div_self h0]
  have emul : ∀ b b' : B, e (b * b') = e b * e b' := by
    intro b b'
    have h := hη b (fun x => f₀ ((b' : G)⁻¹ * x)) g₀
    rw [hη b' f₀ g₀] at h
    have h2 : e (b * b') * P f₀ g₀ = e b * e b' * P f₀ g₀ := by
      rw [← hη, mul_assoc, ← h]
      congr 1
      funext x
      simp [mul_assoc]
    exact mul_right_cancel₀ h0 h2
  let η : B →* ℂ := { toFun := e, map_one' := e1, map_mul' := emul }
  refine ⟨hκ1, η, fun b f g => hη b f g, ⟨K, K.isOpen, fun b hb => ?_⟩, fun b b' hbb => ?_⟩
  · show e b = 1
    rw [he]
    dsimp only
    have hfix : (fun x => f₀ ((b : G)⁻¹ * x)) = f₀ :=
      funext fun x => hKf _ (K.inv_mem (by exact hb)) x
    rw [hfix, div_self h0]
  · show e b' = e b
    have hg1 : s (s^[p - 1] g₀) = g₀ := by
      rw [← Function.iterate_succ_apply' (f := s), Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper]
    have hA := hη b (f₀ ∘ s) (s^[p - 1] g₀)
    rw [hs, hg1] at hA
    have hfun : (fun x => (f₀ ∘ s) ((b : G)⁻¹ * x)) = (fun x => f₀ ((b' : G)⁻¹ * x)) ∘ s := by
      funext x
      simp [hbb, map_mul, map_inv]
    rw [hfun, hs, hg1, hη b' f₀ g₀] at hA
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have h3 : e b' * P f₀ g₀ = e b * P f₀ g₀ := by
      have := mul_left_cancel₀ hκ0 (hA.trans (by ring : e b * (↑κ * P f₀ g₀) = ↑κ * (e b * P f₀ g₀)))
      exact this
    exact mul_right_cancel₀ h0 h3
end

section
noncomputable section

open UpperTheory.ConvolutionTheory.Loc Matrix
open GroundTheory.Automorphic (permGL permGL_apply)
open DoubleCoset (doubleCoset mem_doubleCoset)

namespace UpperTheory.Gal.LocD

section SlopeTestRemainingChoices

variable {E : Type} [Field E] {n : ℕ}

private theorem mem_blockUpper_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ) ↔ g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_borel]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

private theorem mem_autBorel_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.borel n E ↔ g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GroundTheory.Automorphic.mem_borel_iff, GlobalTheory.SmGL.mem_borel E]

private theorem mem_unipotent_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.Iwasawa.unipotent E n ↔ g ∈ GlobalTheory.SmGL.unipB E (Fin n) := by
  rw [GroundTheory.Automorphic.Iwasawa.mem_unipotent, GlobalTheory.SmGL.mem_unipB E]
  exact Iff.rfl

private theorem unipB_le_borel {g : GL (Fin n) E} (hg : g ∈ GlobalTheory.SmGL.unipB E (Fin n)) :
    g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GlobalTheory.SmGL.mem_unipB] at hg
  rw [GlobalTheory.SmGL.mem_borel]
  exact hg.1

private theorem doubleCoset_eq_cell (w : Equiv.Perm (Fin n)) :
    doubleCoset (permGL E w) (GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ) : Set (GL (Fin n) E))
        (GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) =
      cell (GlobalTheory.SmGL.borel E (Fin n)) (GlobalTheory.SmGL.unipB E (Fin n)) (permGL E w) := by
  have hset : ((GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) : Set (GL (Fin n) E)) =
      ((GroundTheory.Automorphic.borel n E) : Set (GL (Fin n) E)) := by
    ext g
    simp only [SetLike.mem_coe]
    rw [mem_blockUpper_iff, mem_autBorel_iff]
  ext g
  constructor
  · intro hg
    rw [hset, GroundTheory.Automorphic.Whittaker.mem_doubleCoset_iff_normalForm] at hg
    obtain ⟨u, hu, t, v, hv, rfl⟩ := hg
    refine ⟨u * GroundTheory.Automorphic.Iwasawa.diagGL E n t, ?_, v, ?_, rfl⟩
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact unipB_le_borel (mem_unipotent_iff.mp hu)
      · exact mem_autBorel_iff.mp (GroundTheory.Automorphic.Whittaker.diagGL_mem_borel t)
    · exact mem_unipotent_iff.mp hv
  · rintro ⟨b, hb, u, hu, rfl⟩
    rw [mem_doubleCoset]
    exact ⟨b, mem_blockUpper_iff.mpr hb, u, mem_blockUpper_iff.mpr (unipB_le_borel hu), rfl⟩

private theorem sg_permGL (σ : E ≃+* E) (w : Equiv.Perm (Fin n)) : sg σ (permGL E w) = permGL E w := by
  ext i j
  rw [sg_val, permGL_apply]
  split_ifs <;> simp

end SlopeTestRemainingChoices

theorem gLCells : GLCells := by
  intro E _ _ _ _ n σ
  haveI : T2Space E := GroundTheory.Automorphic.GLnLocal.t2Space E
  obtain ⟨k, w, hcov, hanti⟩ :=
    GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := E) (Fin.val : Fin n → ℕ) Fin.val
  have hcl := GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨k, fun j => permGL E (w j), fun j => sg_permGL σ _, fun g => ?_, fun j => ?_⟩
  · simpa only [doubleCoset_eq_cell] using hcov g
  · simpa only [doubleCoset_eq_cell] using hcl j

end UpperTheory.Gal.LocD

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private theorem continuous_of_isom (σ : E ≃+* E) (h : Isom σ) : Continuous σ := by
  have h0 : ContinuousAt ((σ : E →+* E) : E →+ E) 0 := by
    rw [ContinuousAt, map_zero]
    intro s hs
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hs
    refine Filter.mem_map.2 ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun x hx => hγ ?_⟩)
    change valuation E (σ x) < γ
    rw [h x]
    exact hx
  exact continuous_of_continuousAt_zero ((σ : E →+* E) : E →+ E) h0

private theorem continuous_sg (σ : E ≃+* E) (h : Continuous σ) : Continuous (sg (n := n) σ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    exact h.comp (Units.continuous_val.matrix_elem i j)
  · have he : ∀ g : GL (Fin n) E, (((sg σ g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
        ((sg σ g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := fun g => by rw [map_inv]
    refine continuous_matrix fun i j => ?_
    simp only [he, sg_val]
    exact h.comp ((Units.continuous_val.comp continuous_inv).matrix_elem i j)

private theorem sg_iterate (σ : E ≃+* E) (i : ℕ) (g : GL (Fin n) E) (a b : Fin n) :
    (((sg σ)^[i] g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) a b =
      σ^[i] ((g : Matrix (Fin n) (Fin n) E) a b) := by
  induction i generalizing g with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, sg_val]

private theorem isClosed_borel : IsClosed (borel E (Fin n) : Set (GL (Fin n) E)) := by
  have : (borel E (Fin n) : Set (GL (Fin n) E)) =
      ⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) E | g.val i j = 0} := by
    ext g
    simp only [SetLike.mem_coe, mem_borel, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

private theorem isClosed_unipB : IsClosed (unipB E (Fin n) : Set (GL (Fin n) E)) := by
  have : (unipB E (Fin n) : Set (GL (Fin n) E)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin n) E | g.val i j = 0}) ∩
        ⋂ i, {g : GL (Fin n) E | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun i => isClosed_eq (Units.continuous_val.matrix_elem i i) continuous_const)

private theorem whitChar_sg (σ : E ≃+* E) (ψ : AddChar E Circle) (hψ : ∀ x, ψ (σ x) = ψ x)
    (u u' : unipB E (Fin n)) (h : (u' : GL (Fin n) E) = sg σ u) : whitChar ψ n u' = whitChar ψ n u := by
  have hs : ∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, (u' : GL (Fin n) E).val p.1 p.2 =
      σ (∑ p : Fin n × Fin n with (p.2 : ℕ) = p.1 + 1, (u : GL (Fin n) E).val p.1 p.2) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [h]; rfl
  change Circle.toUnits (ψ _) = Circle.toUnits (ψ _)
  rw [hs, hψ]

theorem gLFacts : GLFacts := by
  intro E _ _ _ _ n
  refine ⟨isClosed_borel, isClosed_unipB, ⟨GroundTheory.Automorphic.GLnLocal.integralGL E n,
    GroundTheory.Automorphic.GLnLocal.isOpen_integralGL E n, GroundTheory.Automorphic.GLnLocal.isCompact_integralGL E n, fun g => ?_⟩,
    fun ψ hψ => GlobalTheory.Whittaker.isSmoothChar_whitChar hψ, fun σ q hq => ⟨continuous_sg σ (continuous_of_isom σ hq.isom),
      fun g => ?_, fun b hb => ?_, fun ψ hψ u u' h => whitChar_sg σ ψ hψ u u' h⟩⟩
  · obtain ⟨b, hb, k, hk, e⟩ := GroundTheory.Automorphic.Iwasawa.exists_borel_mul_integralGL E n g
    exact ⟨b, (mem_borel E).2 fun i j h => hb h, k, hk, e⟩
  · exact Units.ext (Matrix.ext fun a c => by rw [sg_iterate, hq.ord])
  · exact (mem_borel E).2 fun i j h => by rw [sg_val, (mem_borel E).1 hb i j h, map_zero]

end UpperTheory.Gal.LocD

end
end

section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.eig :
    EigZero → Eig := by
  intro hE T J _ _ _ _ _ ρ s A hA hμs
  obtain ⟨μ, l0, hl0, hl0eq, hgen⟩ := hE T J ρ
  have hμ : ∀ t, μ (s t) = μ t := hμs μ hgen
  let W : Submodule ℂ (Module.Dual ℂ J) :=
    { carrier := {l | ∀ t y, l (ρ t y) = (μ t : ℂ) * l y}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.add_apply, ha t y, hb t y]
        ring
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro t y
        simp
      smul_mem' := by
        intro c l hl
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.smul_apply, smul_eq_mul, hl t y]
        ring }
  have hAW : ∀ l ∈ W, LinearMap.dualMap A l ∈ W := by
    intro l hl t y
    show l (A (ρ t y)) = (μ t : ℂ) * l (A y)
    rw [hA, hl, hμ]
  let A' : W →ₗ[ℂ] W := (LinearMap.dualMap A).restrict hAW
  haveI : Nontrivial W := ⟨⟨⟨l0, hl0eq⟩, 0, fun h => hl0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A'
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨μ, (v : Module.Dual ℂ J), c, fun h => hv.2 (Subtype.ext h), hμ, v.2, fun y => ?_⟩
  have := congrArg (fun w : W => (w : Module.Dual ℂ J) y) hv.apply_eq_smul
  simpa [A'] using this
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.ConvolutionTheory.Loc

namespace UpperTheory.Gal.LocD

section

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

private def dg (E : Type) [Field E] (n : ℕ) : borel E (Fin n) →* (Fin n → Eˣ) :=
  (leviTorus E (Fin n)).symm.toMonoidHom.comp (leviProj E (points (Fin n)))

private theorem dg_val (b : borel E (Fin n)) (i : Fin n) :
    ((dg E n b i : Eˣ) : E) = ((b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i i := by
  show (GeneralLinearGroup.det (leviProj E (points (Fin n)) b i) : E) = _
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_unique]
  exact leviProj_apply E (points (Fin n)) b i _ _

private theorem absPow_map (σ : E ≃+* E) (hσ : Isom σ) (s : ℂ) (x : Eˣ) :
    absPow E s (Units.map (σ : E →* E) x) = absPow E s x := by
  have hv : valuation E ((Units.map (σ : E →* E) x * x⁻¹ : Eˣ) : E) = 1 := by
    have hx : valuation E (x : E) ≠ 0 := by simp
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    rw [hσ]
    exact mul_inv_cancel₀ hx
  have h1 := isUnram_absPow E s _ hv
  have h2 : Units.map (σ : E →* E) x = (Units.map (σ : E →* E) x * x⁻¹) * x := by group
  rw [h2, map_mul, h1, one_mul]

private def dl (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) :
    borel E (Fin n) →* ℂˣ :=
  (deltaHalf E (fun _ : Fin n => Unit)).comp (leviProj E (points (Fin n)))

private theorem dl_eq (b : borel E (Fin n)) :
    dl E n b = ∏ i, absPow E ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) (dg E n b i) :=
  deltaHalf_apply E _

end

theorem toBorel : ToBorel := by
  intro E _ _ _ _ n σ hσ V _ _ π μ hμ l hl
  refine ⟨dl E n * μ.comp (dg E n), ?_, ?_⟩
  · intro b b' hbb'
    have hd : dg E n b' = fun i => Units.map (σ : E →* E) (dg E n b i) := by
      funext i
      ext
      rw [dg_val, hbb', Units.coe_map, dg_val]
      simp only [sg, Matrix.GeneralLinearGroup.map_apply]
      rfl
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, dl_eq, hd, hμ, absPow_map σ hσ]
  · intro b v
    obtain ⟨u, hu, hbu⟩ := exists_levi_mul_unip E (points (Fin n)) b
    have hq : (Submodule.Quotient.mk (π u v) : Jacquet π (unipB E (Fin n))) = Submodule.Quotient.mk v := by
      rw [Submodule.Quotient.eq]
      apply Submodule.subset_span
      exact ⟨⟨u, hu⟩, v, by simp⟩
    have hL : leviTorus E (Fin n) (dg E n b) = leviProj E (points (Fin n)) b :=
      MulEquiv.apply_symm_apply _ _
    have ht : jacB π (dg E n b) (Submodule.Quotient.mk (π u v))
        = jac (points (Fin n)) π (leviProj E (points (Fin n)) b) (Submodule.Quotient.mk (π u v)) := by
      show jac (points (Fin n)) π (leviTorus E (Fin n) (dg E n b)) _ = _
      exact congrArg (fun g => jac (points (Fin n)) π g (Submodule.Quotient.mk (π u v))) hL
    have h2 : l (jacB π (dg E n b) (Submodule.Quotient.mk (π u v)))
        = (((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b))⁻¹ : ℂˣ) : ℂ)
          * l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v))) := by
      rw [ht, jac_mk]
      exact map_smul l _ _
    have hX : l (Submodule.Quotient.mk ((π (leviEmb E (points (Fin n)) (leviProj E (points (Fin n)) b))) (π u v)) : Jacquet π (unipB E (Fin n)))
        = ((deltaHalf E (fun _ : Fin n => Unit) (leviProj E (points (Fin n)) b) : ℂˣ) : ℂ)
          * ((μ (dg E n b) : ℂ) * l (Submodule.Quotient.mk v)) := by
      rw [← hq, ← hl, h2, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [hbu, map_mul, Module.End.mul_apply, hX, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, mul_assoc]
    rfl

end UpperTheory.Gal.LocD

end
end

section
namespace UpperTheory.Gal.LocD

theorem tracePow : TracePow := by
  intro J _ _ _ _ φ hφ k₀
  by_contra hne
  push_neg at hne
  set p := φ.charpoly with hp
  have hc : p.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hm0⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff φ).1
      (by rw [Polynomial.constantCoeff_apply]; exact h0)
    exact hm (hφ (by rw [hm0, map_zero]))
  set t : Polynomial ℂ := -Polynomial.C (p.coeff 0)⁻¹ * Polynomial.divX p with ht
  have hinv : φ * Polynomial.aeval φ t = 1 := by
    have h := congrArg (Polynomial.aeval φ) (Polynomial.X_mul_divX_add p)
    rw [hp, LinearMap.aeval_self_charpoly, ← hp] at h
    simp only [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    have h' : φ * Polynomial.aeval φ (Polynomial.divX p) = -(algebraMap ℂ _ (p.coeff 0)) :=
      eq_neg_of_add_eq_zero_left h
    rw [ht, map_mul, map_neg, Polynomial.aeval_C, neg_mul, mul_neg, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, h', mul_neg, neg_neg, ← map_mul, inv_mul_cancel₀ hc,
      map_one]
  set Q : Polynomial ℂ := (Polynomial.X * t) ^ k₀ with hQ
  have hQ1 : Polynomial.aeval φ Q = 1 := by
    rw [hQ, map_pow, map_mul, Polynomial.aeval_X, hinv, one_pow]
  have htr : LinearMap.trace ℂ J (Polynomial.aeval φ Q) = 0 := by
    rw [Polynomial.aeval_eq_sum_range, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
    by_cases hi : k₀ ≤ i
    · rw [hne i hi, mul_zero]
    · rw [hQ, mul_pow, Polynomial.coeff_X_pow_mul', if_neg hi, zero_mul]
  rw [hQ1, LinearMap.trace_one] at htr
  exact (Nat.cast_ne_zero.2 (Module.finrank_pos (R := ℂ) (M := J)).ne') htr

end UpperTheory.Gal.LocD
end

section
namespace UpperTheory.Gal.LocD

theorem funInv_holds : FunInv := by
  have dist := distInv (distZero (cellStep stabSub))
  exact funInv (biInv dist) prMem prLeft prAuto prSurj etaEx

theorem scalar_holds : Scalar := by
  have fi := funInv_holds
  exact scalar_of (eig eigZero) toBorel jacSemi (core fi gLCells gLFacts)

theorem locDesc_holds : LocDesc := locDesc_of scalar_holds tracePow

theorem ofSupport_holds : OfSupport := ofSupport

end UpperTheory.Gal.LocD
end
