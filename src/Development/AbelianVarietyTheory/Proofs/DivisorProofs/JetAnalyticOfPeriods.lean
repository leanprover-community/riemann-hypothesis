import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOfHilbertBlumenthal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateExistenceOfPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetDeterminantOfDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertUniformization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertRealMultiplication
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An GlobalTheory.RealMult
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD polydisc)
open scoped Classical Topology

namespace GlobalTheory.LatJet.An

theorem analyticAt_of_differentiableOn_fin {I : Type} [Fintype I] {U : Set (I → ℂ)} (hU : IsOpen U)
    {f : (I → ℂ) → ℂ} (hf : DifferentiableOn ℂ f U) {z : I → ℂ} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  let e : (Fin (Fintype.card I) → ℂ) ≃L[ℂ] (I → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : I => ℂ) (Fintype.equivFin I).symm
  have hs : AnalyticAt ℂ (⇑e.symm) z := (e.symm : (I → ℂ) →L[ℂ] (Fin (Fintype.card I) → ℂ)).analyticAt z
  have hU' : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hd : DifferentiableOn ℂ (f ∘ e) (e ⁻¹' U) := hf.comp e.differentiableOn (fun _ h => h)
  have ha : AnalyticAt ℂ (f ∘ e) (e.symm z) :=
    ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU' hd _ (by simpa using hz)
  exact (ha.comp hs).congr
    (Filter.Eventually.of_forall fun w => by simp)

theorem isOpen_polydisc (I : Type) [Fintype I] : IsOpen (polydisc I) := by
  simp only [polydisc, Set.setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i).norm continuous_const

theorem zero_mem_polydisc (I : Type) : (0 : I → ℂ) ∈ polydisc I := fun i => by simp

theorem jetAnalytic_of_steps (hC : JetCalc) (hCh : JetChain) (hG : GermEx) (hK : CoordEx) (hZ : JetZeta) (hD : JetDet)
    (hS : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement) : JetAnalytic := by
  obtain ⟨ε₀, hK⟩ := hK
  obtain ⟨s₀, hZ⟩ := hZ
  refine ⟨s₀ * ε₀, ?_⟩
  intro E _ _ _ I _ 𝔠 φ c y hf hCM hc R₀ s r m hs hr T n J Y _ hR₀ g ν u hg hu
  obtain ⟨G⟩ := hG E I 𝔠 φ c y hCM hc n T J Y
  obtain ⟨K⟩ := hK E I 𝔠 φ c y hCM hc n T J Y G
  have hζ := hZ ε₀ E I 𝔠 φ c y hCM hc n T J Y G K
  obtain ⟨hCan, hCe⟩ := hD ε₀ E I 𝔠 φ c y hCM hc n T J Y G K
  obtain ⟨-, hprod, hev, hconst, -, -, -⟩ := hC I n J
  have hgd : DifferentiableOn ℂ g (polydisc I) := ((((hS E I φ hf hCM).1 s hs).1 c y hc).1.2 g hg).1
  have hgan : AnalyticAt ℂ g 0 := analyticAt_of_differentiableOn_fin (isOpen_polydisc I) hgd (zero_mem_polydisc I)
  have hζan : AnalyticAt ℂ K.ζ 0 := by
    rw [analyticAt_pi_iff]
    intro i
    exact analyticAt_of_differentiableOn_fin K.isOpen (differentiableOn_pi.1 K.ζ_hol i) K.zero
  letI : Algebra R₀ G.B := ((algebraMap ℂ G.B).comp R₀.subtype).toAlgebra
  have hfan : AnalyticAt ℂ (fun z => G.y z (r.val G.B G.X trivial G.δ)) 0 :=
    analyticAt_of_differentiableOn_fin G.isOpen (G.hol _) G.zero
  have hfib : ∀ z ∈ K.V, K.C z ^ (2 * s) * G.y z (r.val G.B G.X trivial G.δ) = m * g (K.ζ z) := by
    intro z hz
    have hcomm : ∀ x : R₀, G.y z (algebraMap R₀ G.B x) = algebraMap R₀ ℂ x := fun x => by
      show G.y z (algebraMap ℂ G.B (x : ℂ)) = _
      rw [AlgHom.commutes]; rfl
    let σ : G.B →ₐ[R₀] ℂ := { (G.y z : G.B →+* ℂ) with commutes' := hcomm }
    have hb := r.baseChange G.B ℂ σ G.X trivial (K.X z) trivial (K.q z) G.δ (K.δ z) (K.pull z) (K.corr z)
    rw [← hr g hg (K.ζ z) (K.ζ_mem z hz) (K.X z) (K.U z hz) (K.δ z) (K.C z) (K.det z hz), hb]
    rfl
  have hjB : r.val J.B Y.X' trivial G.δ'' = G.j (r.val G.B G.X trivial G.δ) := by
    have hcomm : ∀ x : R₀, G.j (algebraMap R₀ G.B x) = algebraMap R₀ J.B x := fun x => by
      show G.j (algebraMap ℂ G.B (x : ℂ)) = _
      rw [AlgHom.commutes, hR₀]
    let σ : G.B →ₐ[R₀] J.B := { (G.j : G.B →+* J.B) with commutes' := hcomm }
    exact r.baseChange G.B J.B σ G.X trivial Y.X' trivial G.q G.δ G.δ'' G.pull G.corr
  have hhom := r.homog J.B Y.X' trivial G.δ'' Y.δ' G.e G.he
  have hpow : ∀ k : ℕ, jet J (fun z => K.C z ^ k) = jet J K.C ^ k := by
    intro k
    induction k with
    | zero => simpa using hconst 1
    | succ k ih =>
      have e1 : (fun z => K.C z ^ (k + 1)) = (fun z => K.C z ^ k) * K.C := by
        funext z; simp [pow_succ]
      rw [e1, (hprod (fun z => K.C z ^ k) K.C (hCan.pow k) hCan).1, ih, pow_succ]
  have hgζ : AnalyticAt ℂ (g ∘ K.ζ) 0 := by
    have : AnalyticAt ℂ g (K.ζ 0) := by rw [K.ζ_zero]; exact hgan
    exact this.comp hζan
  have hevq : (fun z => K.C z ^ (2 * s)) * (fun z => G.y z (r.val G.B G.X trivial G.δ)) =ᶠ[𝓝 0]
      (fun _ => m) * (g ∘ K.ζ) := by
    filter_upwards [K.isOpen.mem_nhds K.zero] with z hz using hfib z hz
  have hmain : algebraMap ℂ J.B (T.C ^ (2 * s)) * r.val J.B Y.X' trivial Y.δ' =
      algebraMap ℂ J.B m * jet J (g ∘ K.ζ) := by
    calc algebraMap ℂ J.B (T.C ^ (2 * s)) * r.val J.B Y.X' trivial Y.δ'
        = (G.e * jet J K.C) ^ (2 * s) * r.val J.B Y.X' trivial Y.δ' := by rw [map_pow, hCe]
      _ = jet J K.C ^ (2 * s) * (G.e ^ (2 * s) * r.val J.B Y.X' trivial Y.δ') := by ring
      _ = jet J (fun z => K.C z ^ (2 * s)) * jet J (fun z => G.y z (r.val G.B G.X trivial G.δ)) := by
        rw [hhom, hjB, G.jet_eq, hpow]
      _ = jet J ((fun z => K.C z ^ (2 * s)) * (fun z => G.y z (r.val G.B G.X trivial G.δ))) :=
        ((hprod (fun z => K.C z ^ (2 * s)) _ (hCan.pow _) hfan).1).symm
      _ = jet J ((fun _ => m) * (g ∘ K.ζ)) := hev _ _ hevq
      _ = algebraMap ℂ J.B m * jet J (g ∘ K.ζ) := by rw [(hprod _ _ analyticAt_const hgζ).1, hconst]
  have hrep := congrArg (fun x => J.b.repr x ν) hmain
  simp only [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul] at hrep
  rw [hrep, hCh I n J K.ζ (fun i => (((s₀ * ε₀ : ℤˣ) : ℤ) : ℂ) * T.A i) g hζan K.ζ_zero hgan (fun i => hζ i) ν u hu]
  ring

end GlobalTheory.LatJet.An
end
end

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical Topology ContDiff

namespace GlobalTheory.LatJet.An.Chain

variable {I : Type} [Fintype I]

theorem iterD_ofFn {f : (I → ℂ) → ℂ} {U : Set (I → ℂ)} (hU : IsOpen U) (hf : ContDiffOn ℂ ω f U) :
    ∀ (k : ℕ) (s : Fin k → I), ∀ z ∈ U,
      iterD (List.ofFn s) f z = iteratedFDeriv ℂ k f z (fun a => Pi.single (s a) 1) := by
  intro k
  induction k with
  | zero => intro s z _; simp [iterD]
  | succ k ih =>
    intro s z hz
    have hev : iterD (List.ofFn (Fin.tail s)) f =ᶠ[𝓝 z]
        fun w => iteratedFDeriv ℂ k f w (fun a => Pi.single (Fin.tail s a) 1) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) (ih (Fin.tail s))
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k f) z :=
      (((hf.contDiffAt (hU.mem_nhds hz)).iteratedFDeriv_right (m := 1) (i := k) le_top)).differentiableAt one_ne_zero
    have e1 : iterD (List.ofFn s) f z = partialD (s 0) (iterD (List.ofFn (Fin.tail s)) f) z := by
      rw [List.ofFn_succ]; rfl
    rw [e1, partialD, hev.lineDeriv_eq, (hd.continuousMultilinear_apply_const _).lineDeriv_eq_fderiv,
      fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
    rfl

theorem iterD_ofFn_zero {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (k : ℕ) (s : Fin k → I) :
    iterD (List.ofFn s) f 0 = iteratedFDeriv ℂ k f 0 (fun a => Pi.single (s a) 1) := by
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  exact iterD_ofFn Metric.isOpen_ball (hfr.contDiffOn Metric.isOpen_ball.uniqueDiffOn) k s 0
    (Metric.mem_ball_self hr)

theorem sum_count (l : List I) : ∑ i, l.count i = l.length := by
  induction l with
  | nil => simp
  | cons j l ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

theorem prod_get (a : I → ℂ) (l : List I) : ∏ b : Fin l.length, a (l.get b) = ∏ i, a i ^ l.count i := by
  rw [show (∏ b : Fin l.length, a (l.get b)) = (l.map a).prod by simpa using Fin.prod_univ_fun_getElem l a]
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    simp only [List.count_cons, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single j (fun b _ hb => by simp [beq_iff_eq, Ne.symm hb]) (by simp)]
    simp

theorem iteratedFDeriv_coord {f : (I → ℂ) → I → ℂ} (hf : ContDiffAt ℂ ω f 0) (k : ℕ) (i : I)
    (m : Fin k → I → ℂ) : iteratedFDeriv ℂ k (fun z => f z i) 0 m = iteratedFDeriv ℂ k f 0 m i := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).iteratedFDeriv_comp_left hf
    (i := k) le_top
  exact congrArg (fun L => L m) h

theorem iteratedFDeriv_comp_clm {f : (I → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (A : (I → ℂ) →L[ℂ] (I → ℂ))
    (k : ℕ) : iteratedFDeriv ℂ k (f ∘ A) 0 = (iteratedFDeriv ℂ k f 0).compContinuousLinearMap fun _ => A := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (k : WithTop ℕ∞)) le_top (fun _ => rfl)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hs : IsOpen (Metric.ball (0 : I → ℂ) r) := Metric.isOpen_ball
  have h0 : (0 : I → ℂ) ∈ Metric.ball (0 : I → ℂ) r := Metric.mem_ball_self hr
  have hpre : IsOpen (A ⁻¹' Metric.ball (0 : I → ℂ) r) := hs.preimage A.continuous
  have h0' : (0 : I → ℂ) ∈ A ⁻¹' Metric.ball (0 : I → ℂ) r := by simpa using h0
  have key := A.iteratedFDerivWithin_comp_right (hfu.mono hball) hs.uniqueDiffOn hpre.uniqueDiffOn h0'
    (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hpre h0', map_zero, iteratedFDerivWithin_of_isOpen k hs h0] at key
  exact key

theorem iteratedFDeriv_comp_congr {g : (I → ℂ) → ℂ} {f₁ f₂ : (I → ℂ) → I → ℂ}
    (hg : ContDiffAt ℂ ω g 0) (h₁ : ContDiffAt ℂ ω f₁ 0) (h₂ : ContDiffAt ℂ ω f₂ 0)
    (e₁ : f₁ 0 = 0) (e₂ : f₂ 0 = 0) (N : ℕ)
    (h : ∀ k ≤ N, iteratedFDeriv ℂ k f₁ 0 = iteratedFDeriv ℂ k f₂ 0) :
    ∀ k ≤ N, iteratedFDeriv ℂ k (g ∘ f₁) 0 = iteratedFDeriv ℂ k (g ∘ f₂) 0 := by
  intro k hk
  rw [iteratedFDeriv_comp (by rw [e₁]; exact hg) h₁ le_top, iteratedFDeriv_comp (by rw [e₂]; exact hg) h₂ le_top, e₁, e₂]
  unfold FormalMultilinearSeries.taylorComp
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : (fun m => ftaylorSeries ℂ f₁ 0 (c.partSize m)) = fun m => ftaylorSeries ℂ f₂ 0 (c.partSize m) :=
    funext fun m => h _ ((c.partSize_le m).trans hk)
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition, hc]

theorem jetChain_of_jetCalc : JetCalc → JetChain := by
  intro hC I _ n J ζ a g hζ hζ0 hg hjet ν u hu
  obtain ⟨h1, h2, -, h4, h5, -, -⟩ := hC I n J
  let Λ : (I → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i => a i • ContinuousLinearMap.proj i
  have hΛ : ∀ z i, Λ z i = a i * z i := fun z i => by simp [Λ]
  have hpr : ∀ i, AnalyticAt ℂ (fun z : I → ℂ => z i) 0 := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt 0
  have hΛjet : ∀ i, jet J (fun z => Λ z i) = a i • J.t i := by
    intro i
    have e : (fun z : I → ℂ => Λ z i) = (fun _ => a i) * (fun z => z i) := by funext z; simp [hΛ]
    rw [e, (h2 _ _ analyticAt_const (hpr i)).1, h4, h5, Algebra.smul_def]
  have hζi : ∀ i, AnalyticAt ℂ (fun z => ζ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt (ζ 0)).comp hζ
  have hΛi : ∀ i, AnalyticAt ℂ (fun z => Λ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt (Λ 0)).comp (Λ.analyticAt 0)
  have hD : ∀ i k, k ≤ n + 1 → iteratedFDeriv ℂ k (fun z => ζ z i) 0 = iteratedFDeriv ℂ k (fun z => Λ z i) 0 := by
    intro i k hk
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ I) fun s => ?_
    simp only [ContinuousMultilinearMap.coe_coe, Pi.basisFun_apply]
    rw [← iterD_ofFn_zero (hζi i) k s, ← iterD_ofFn_zero (hΛi i) k s]
    have hν : ∑ j, (List.ofFn s).count j ≤ n + 1 := by rw [sum_count, List.length_ofFn]; exact hk
    rw [← h1 _ (hζi i) ⟨_, hν⟩ _ (fun _ => rfl), ← h1 _ (hΛi i) ⟨_, hν⟩ _ (fun _ => rfl), hjet i, hΛjet i]
  have hDv : ∀ k ≤ n + 1, iteratedFDeriv ℂ k ζ 0 = iteratedFDeriv ℂ k Λ 0 := by
    intro k hk
    ext m i
    rw [← iteratedFDeriv_coord hζ.contDiffAt, ← iteratedFDeriv_coord (Λ.analyticAt 0).contDiffAt, hD i k hk]
  have hk : u.length ≤ n + 1 := by
    rw [← sum_count u]; simp only [hu]; exact ν.2
  have hgz : AnalyticAt ℂ (g ∘ ζ) 0 := by
    refine AnalyticAt.comp ?_ hζ
    rw [hζ0]; exact hg
  rw [h1 _ hgz ν u hu]
  have e : ∀ f, iterD u f 0 = iterD (List.ofFn u.get) f 0 := by intro f; rw [List.ofFn_get]
  rw [e, e, iterD_ofFn_zero hgz, iterD_ofFn_zero hg,
    iteratedFDeriv_comp_congr hg.contDiffAt hζ.contDiffAt (Λ.analyticAt 0).contDiffAt hζ0 (map_zero Λ) (n + 1)
      hDv _ hk, iteratedFDeriv_comp_clm hg.contDiffAt]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun b : Fin u.length => Λ (Pi.single (u.get b) 1)) = fun b => a (u.get b) • Pi.single (u.get b) 1 := by
    funext b; ext i; rw [hΛ]
    by_cases h : i = u.get b
    · subst h; simp
    · simp only [List.get_eq_getElem] at h; simp [Pi.single_apply, h]
  rw [hv, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, prod_get, mul_comm]
  simp only [hu]

end GlobalTheory.LatJet.An.Chain
end
end

section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open scoped Topology

namespace GlobalTheory.LatJet.An.HolLiftProof

theorem ker_nil (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n) : IsNilpotent (RingHom.ker J.π) := by
  classical
  haveI : Finite (Idx I n) := by
    refine Finite.of_injective (fun ν : Idx I n ↦ fun i ↦ (⟨ν.1 i, Nat.lt_succ_of_le (le_trans
      (Finset.single_le_sum (fun l _ ↦ Nat.zero_le (ν.1 l)) (Finset.mem_univ i)) ν.2)⟩ : Fin (n + 2))) ?_
    intro a b h
    exact Subtype.ext (funext fun i ↦ by simpa using congrFun h i)
  haveI : Module.Finite ℂ J.B := Module.Finite.of_basis J.b
  haveI : IsNoetherian ℂ J.B := IsNoetherian.iff_fg.2 inferInstance
  haveI : IsNoetherianRing J.B := isNoetherian_of_tower ℂ inferInstance
  rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian (RingHom.ker J.π))]
  intro x hx
  obtain ⟨N, hN⟩ := J.nil
  refine mem_nilradical.2 ⟨N, ?_⟩
  have := hN (List.replicate N (1, x)) (fun p hp ↦ by rw [List.eq_of_mem_replicate hp]; exact hx) (by simp)
  simpa [List.map_replicate, J.κ.dpow_one hx] using this

theorem adjoin_top (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n) :
    Algebra.adjoin ℂ (Set.range J.t) = ⊤ := by
  classical
  set A := Algebra.adjoin ℂ (Set.range J.t)
  have key : ∀ k, ∀ ν : Idx I n, ∑ i, ν.1 i = k → J.b ν ∈ A := by
    intro k
    induction k with
    | zero =>
      intro ν hν
      have : ν = ⟨0, by simp⟩ :=
        Subtype.ext (funext fun i ↦ (Finset.sum_eq_zero_iff.1 hν) i (Finset.mem_univ i))
      rw [this, J.one]; exact A.one_mem
    | succ k ih =>
      intro ν hν
      obtain ⟨i, hi⟩ : ∃ i, ν.1 i ≠ 0 := by
        by_contra h; push_neg at h; simp [h] at hν
      let ν' : Idx I n := ⟨ν.1 - Pi.single i 1,
        le_trans (Finset.sum_le_sum fun l _ ↦ Nat.sub_le (ν.1 l) _) ν.2⟩
      have hsum : ν.1 = Pi.single i 1 + ν'.1 := by
        funext l
        by_cases hl : l = i
        · subst hl; simp [ν']; omega
        · simp [ν', hl]
      have hν' : ∑ l, ν'.1 l = k := by
        have : ∑ l, ν.1 l = ∑ l, (Pi.single i 1 : I → ℕ) l + ∑ l, ν'.1 l := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ ↦ congrFun hsum l
        simp at this; omega
      have hmul := J.mul ⟨Pi.single i 1, by simp⟩ ν'
      have hle : ∑ l, ((Pi.single i 1 : I → ℕ) + ν'.1) l ≤ n + 1 := by rw [← hsum]; exact ν.2
      rw [dif_pos hle] at hmul
      have hprod : ∏ l, (((Pi.single i 1 : I → ℕ) l + ν'.1 l).choose ((Pi.single i 1 : I → ℕ) l)) = ν.1 i := by
        rw [Finset.prod_eq_single i]
        · simp [ν']; omega
        · intro l _ hl; simp [hl]
        · simp
      have hb : J.b ⟨(Pi.single i 1 : I → ℕ) + ν'.1, hle⟩ = J.b ν := congrArg J.b (Subtype.ext hsum.symm)
      simp only [Pi.add_apply] at hmul
      rw [hprod, hb] at hmul
      have hne : (ν.1 i : ℂ) ≠ 0 := by exact_mod_cast hi
      have : J.b ν = (ν.1 i : ℂ)⁻¹ • (J.t i * J.b ν') := by
        rw [JetRing.t, hmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact A.smul_mem (A.mul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (ih ν' hν')) _
  rw [eq_top_iff]
  intro x _
  have hle : Submodule.span ℂ (Set.range J.b) ≤ Subalgebra.toSubmodule A :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun ν ↦ key _ ν rfl)
  exact hle (J.b.mem_span x)

theorem analyticAt_eval {I : Type} [Fintype I] (Q : MvPolynomial I ℂ) (x : I → ℂ) :
    AnalyticAt ℂ (fun z ↦ MvPolynomial.eval z Q) x := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => exact (hp.add hq).congr (Filter.Eventually.of_forall fun z ↦ by simp)
  | mul_X p i hp =>
    exact (hp.mul ((ContinuousLinearMap.proj i : (I → ℂ) →L[ℂ] ℂ).analyticAt x)).congr
      (Filter.Eventually.of_forall fun z ↦ by simp)

variable {I : Type} [Fintype I] {n : ℕ}

theorem pi_jet (hC : JetCalc) (J : JetRing ℂ I n) (f : (I → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    J.π (jet J f) = f 0 := by
  rw [J.π_eq]
  exact (hC I n J).1 f hf ⟨0, by simp⟩ [] (by simp)

theorem jet_eval (hC : JetCalc) (J : JetRing ℂ I n) (Q : MvPolynomial I ℂ) :
    jet J (fun z ↦ MvPolynomial.eval z Q) = MvPolynomial.aeval J.t Q := by
  obtain ⟨-, h2, -, h4, h5, -⟩ := hC I n J
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, ← h4 a]
    congr 1; funext z; simp
  | add p q hp hq =>
    rw [map_add, ← hp, ← hq, ← (h2 _ _ (analyticAt_eval p 0) (analyticAt_eval q 0)).2]
    congr 1; funext z; simp
  | mul_X p i hp =>
    rw [map_mul, ← hp, MvPolynomial.aeval_X, ← h5 i,
      ← (h2 _ (fun z ↦ z i) (analyticAt_eval p 0)
        ((ContinuousLinearMap.proj i : (I → ℂ) →L[ℂ] ℂ).analyticAt 0)).1]
    congr 1; funext z; simp

def piAlg (hC : JetCalc) (J : JetRing ℂ I n) : J.B →ₐ[ℂ] ℂ :=
  { J.π with
    commutes' := fun a ↦ by
      show J.π (algebraMap ℂ J.B a) = a
      rw [← (hC I n J).2.2.2.1 a]
      exact pi_jet hC J _ analyticAt_const }

end GlobalTheory.LatJet.An.HolLiftProof

namespace GlobalTheory.LatJet.An.HolLiftProof

open GlobalTheory.AffinePoints

variable {I : Type} [Fintype I] {n : ℕ}

theorem isUnit_of_pi_ne_zero (J : JetRing ℂ I n) (x : J.B) (hx : J.π x ≠ 0) : IsUnit x := by
  obtain ⟨N, hN⟩ := ker_nil I n J
  set a := J.π x
  have hr : algebraMap ℂ J.B a⁻¹ * x - 1 ∈ RingHom.ker J.π := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one]
    have : J.π (algebraMap ℂ J.B a⁻¹) = a⁻¹ := by
      rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, J.b.repr_self]
      simp
    rw [this, inv_mul_cancel₀ hx, sub_self]
  have hnil : IsNilpotent (algebraMap ℂ J.B a⁻¹ * x - 1) := by
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow hr N
    rw [hN] at this
    simpa using this
  have hx' : x = algebraMap ℂ J.B a * (1 + (algebraMap ℂ J.B a⁻¹ * x - 1)) := by
    rw [add_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul]
  rw [hx']
  exact ((IsUnit.mk0 a hx).map (algebraMap ℂ J.B)).mul hnil.isUnit_one_add

theorem holLift_std (hC : JetCalc) (B : Type) [CommRing B] [Algebra ℂ B] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d ℂ B] (J : JetRing ℂ I n) (j : B →ₐ[ℂ] J.B) :
    ∃ (U : Set (I → ℂ)) (y : (I → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen U ∧ 0 ∈ U ∧
      (∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U) ∧ ∀ b, j b = jet J fun z ↦ y z b := by
  classical
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d ℂ B
  let p : B →ₐ[ℂ] ℂ := (piAlg hC J).comp j
  obtain ⟨e, hp, he, han⟩ := GlobalTheory.AffinePoints.exists_chart_of_etale g hg p
  have hsurj : ∀ c : J.B, ∃ Q : MvPolynomial I ℂ, MvPolynomial.aeval J.t Q = c := fun c ↦ by
    have : c ∈ Algebra.adjoin ℂ (Set.range J.t) := by rw [adjoin_top]; trivial
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  choose Q hQ using fun k : Fin d ↦ hsurj (j (g (MvPolynomial.X k)))
  let w : (I → ℂ) → Fin d → ℂ := fun z k ↦ MvPolynomial.eval z (Q k)
  have hwan : ∀ x, AnalyticAt ℂ w x := fun x ↦ analyticAt_pi_iff.2 fun k ↦ analyticAt_eval (Q k) x
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun x ↦ (hwan x).continuousAt
  have hw0 : w 0 = e p := by
    funext k
    rw [he, GlobalTheory.AffinePoints.coords_apply]
    show MvPolynomial.eval 0 (Q k) = J.π (j (g (MvPolynomial.X k)))
    rw [← hQ k, ← jet_eval hC J, pi_jet hC J _ (analyticAt_eval _ 0)]
  let U : Set (I → ℂ) := w ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage hwc
  have h0U : (0 : I → ℂ) ∈ U := by
    show w 0 ∈ e.target
    rw [hw0]; exact e.map_source hp
  let y : (I → ℂ) → (B →ₐ[ℂ] ℂ) := fun z ↦ e.symm (w z)
  have hyan : ∀ b, ∀ z ∈ U, AnalyticAt ℂ (fun z ↦ y z b) z := fun b z hz ↦
    (han b (w z) hz).comp (hwan z)
  obtain ⟨-, hmul, hloc, hconst, -⟩ := hC I n J
  let ψ : B →ₐ[ℂ] J.B :=
    { toFun := fun b ↦ jet J fun z ↦ y z b
      map_one' := by
        show (jet J fun z ↦ y z 1) = 1
        rw [show (fun z ↦ y z 1) = fun _ ↦ (1 : ℂ) from funext fun z ↦ map_one _, hconst, map_one]
      map_mul' := fun a b ↦ by
        show (jet J fun z ↦ y z (a * b)) = (jet J fun z ↦ y z a) * jet J fun z ↦ y z b
        rw [show (fun z ↦ y z (a * b)) = (fun z ↦ y z a) * (fun z ↦ y z b) from
          funext fun z ↦ map_mul _ _ _]
        exact (hmul _ _ (hyan a 0 h0U) (hyan b 0 h0U)).1
      map_zero' := by
        show (jet J fun z ↦ y z 0) = 0
        rw [show (fun z ↦ y z 0) = fun _ ↦ (0 : ℂ) from funext fun z ↦ map_zero _, hconst, map_zero]
      map_add' := fun a b ↦ by
        show (jet J fun z ↦ y z (a + b)) = (jet J fun z ↦ y z a) + jet J fun z ↦ y z b
        rw [show (fun z ↦ y z (a + b)) = (fun z ↦ y z a) + (fun z ↦ y z b) from
          funext fun z ↦ map_add _ _ _]
        exact (hmul _ _ (hyan a 0 h0U) (hyan b 0 h0U)).2
      commutes' := fun c ↦ by
        show (jet J fun z ↦ y z (algebraMap ℂ B c)) = algebraMap ℂ J.B c
        rw [show (fun z ↦ y z (algebraMap ℂ B c)) = fun _ ↦ c from
          funext fun z ↦ AlgHom.commutes _ _, hconst] }
  have hψ : ∀ b, ψ b = jet J fun z ↦ y z b := fun b ↦ rfl
  have hcoord : ψ.comp g = j.comp g := by
    apply MvPolynomial.algHom_ext
    intro k
    show (jet J fun z ↦ y z (g (MvPolynomial.X k))) = j (g (MvPolynomial.X k))
    rw [← hQ k, ← jet_eval hC J]
    apply hloc
    filter_upwards [hU.mem_nhds h0U] with z hz
    have := congrFun (e.right_inv hz) k
    rw [he, GlobalTheory.AffinePoints.coords_apply] at this
    exact this
  have hres : ∀ b, J.π (j b) = J.π (ψ b) := fun b ↦ by
    rw [hψ, pi_jet hC J _ (hyan b 0 h0U)]
    show J.π (j b) = e.symm (w 0) b
    rw [hw0, e.left_inv hp]
    rfl
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) B := hg
  letI : Algebra (MvPolynomial (Fin d) ℂ) J.B := (j.comp g).toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin d) ℂ] J.B := { j.toRingHom with commutes' := fun _ ↦ rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin d) ℂ] J.B :=
    { ψ.toRingHom with commutes' := fun q ↦ AlgHom.congr_fun hcoord q }
  have h12 : ψ₁ = ψ₂ := Algebra.FormallyUnramified.ext' J.π (ker_nil I n J) ψ₁ ψ₂ hres
  refine ⟨U, y, hU, h0U, fun b z hz ↦ (hyan b z hz).differentiableAt.differentiableWithinAt, fun b ↦ ?_⟩
  exact AlgHom.congr_fun h12 b

theorem holLift (hC : JetCalc) : HolLift := by
  intro B _ _ _ I _ n J j
  classical
  let p : B →ₐ[ℂ] ℂ := (piAlg hC J).comp j
  haveI := RingHom.ker_isPrime p
  obtain ⟨s, hs, ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℂ (RingHom.ker p)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension ℂ (Localization.Away s) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have hu : IsUnit (j s) := isUnit_of_pi_ne_zero J _ hs
  let j' : Localization.Away s →ₐ[ℂ] J.B := IsLocalization.Away.liftAlgHom s hu
  obtain ⟨U, y', hU, h0U, hd, hj⟩ := holLift_std hC (Localization.Away s) P.dimension J j'
  refine ⟨U, fun z ↦ (y' z).comp (IsScalarTower.toAlgHom ℂ B (Localization.Away s)), hU, h0U,
    fun b ↦ hd _, fun b ↦ ?_⟩
  show j b = jet J fun z ↦ y' z (algebraMap B (Localization.Away s) b)
  rw [← hj]
  simp [j']

end GlobalTheory.LatJet.An.HolLiftProof

theorem GlobalTheory.LatJet.An.holLift_of_jetCalc : JetCalc → HolLift := GlobalTheory.LatJet.An.HolLiftProof.holLift
end
end

section
section
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.LatJet

theorem count_cons_eq_single_add {I : Type} [DecidableEq I] (a : I) (l : List I) (i : I) :
    (a :: l).count i = (Pi.single a 1 : I → ℕ) i + l.count i := by
  rw [List.count_cons]
  by_cases h : i = a
  · subst h; simp [add_comm]
  · have h' : ¬ a = i := fun e => h e.symm
    simp [h, h', Pi.single_apply]

theorem prod_map_t_eq_smul_b : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hc : ∑ i, l.count i ≤ n + 1),
    (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ := by
  intro R _ I _ n J l
  induction l with
  | nil =>
    intro hc
    have : (⟨fun i => List.count i ([] : List I), hc⟩ : Idx I n) = ⟨0, by simp⟩ := by
      apply Subtype.ext; funext i; simp
    rw [this, J.one]; simp
  | cons a l ih =>
    intro hc
    have hc' : ∑ i, l.count i ≤ n + 1 :=
      le_trans (Finset.sum_le_sum fun i _ => List.count_le_count_cons ..) hc
    have hsum : ∑ i, ((Pi.single a 1 : I → ℕ) + fun i => l.count i) i ≤ n + 1 := by
      refine le_of_eq_of_le ?_ hc
      exact Finset.sum_congr rfl fun i _ => (count_cons_eq_single_add a l i).symm
    rw [List.map_cons, List.prod_cons, ih hc', mul_smul_comm, JetRing.t, J.mul, dif_pos hsum,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, ← Nat.cast_mul]
    have hidx : (⟨(Pi.single a 1 : I → ℕ) + fun i => l.count i, hsum⟩ : Idx I n) = ⟨fun i => (a :: l).count i, hc⟩ := by
      apply Subtype.ext; funext i; exact (count_cons_eq_single_add a l i).symm
    have hprod : (∏ i, ((a :: l).count i).factorial) =
        (∏ i, ((Pi.single a 1 : I → ℕ) i + l.count i).choose ((Pi.single a 1 : I → ℕ) i)) * ∏ i, (l.count i).factorial := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [count_cons_eq_single_add]
      by_cases h : i = a
      · subst h; simp [Nat.factorial_succ, add_comm]
      · simp [Pi.single_apply, h]
    rw [hidx, hprod, mul_comm]

end GlobalTheory.LatJet
end

open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_prod_eq_factorial_smul : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I) (hc : ∑ i, l.count i ≤ n + 1), (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ := by
  atlas_forward_decl GlobalTheory.LatJet.prod_map_t_eq_smul_b
end

section
section
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.LatJet.ProdZero

theorem b_mul_prod_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (l : List I) :
    ∀ ν : Idx I n, n + 1 < (∑ i, (ν : I → ℕ) i) + l.length →
      J.b ν * (l.map J.t).prod = 0 := by
  induction l with
  | nil =>
    intro ν h
    exact absurd ν.2 (by simpa using h)
  | cons a l ih =>
    intro ν h
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    have hm := J.mul ν ⟨Pi.single a 1, by
      rw [Finset.sum_pi_single']; simp⟩
    have ht : J.t a = J.b ⟨Pi.single a 1, by rw [Finset.sum_pi_single']; simp⟩ := rfl
    rw [ht, hm]
    by_cases hle : ∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i ≤ n + 1
    · rw [dif_pos hle, smul_mul_assoc, ih _ ?_, smul_zero]
      have hs : ∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i = (∑ i, (ν : I → ℕ) i) + 1 := by
        simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib, Finset.sum_pi_single']
        simp
      show n + 1 < (∑ i, ((ν : I → ℕ) + (Pi.single a 1 : I → ℕ)) i) + l.length
      rw [hs]
      simp only [List.length_cons] at h
      omega
    · rw [dif_neg hle, zero_mul]

theorem prod_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
    (J : JetRing R I n) (l : List I) (h : n + 1 < l.length) :
    (l.map J.t).prod = 0 := by
  have := b_mul_prod_eq_zero J l ⟨0, by simp⟩ (by simpa using h)
  rwa [J.one, one_mul] at this

end GlobalTheory.LatJet.ProdZero
end

open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_prod_eq_zero_of_long : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I), n + 1 < l.length → (l.map J.t).prod = 0 := by
  atlas_forward_decl GlobalTheory.LatJet.ProdZero.prod_eq_zero
end

section
section
open scoped Classical

namespace GlobalTheory.MultinomialCount

theorem ofFn_cons_count {I : Type} {k : ℕ} (a : I) (t : Fin k → I) (i : I) :
    (List.ofFn (Fin.cons a t : Fin (k+1) → I)).count i = (List.ofFn t).count i + if a = i then 1 else 0 := by
  rw [List.ofFn_succ]
  simp [List.count_cons, Fin.cons_zero, Fin.cons_succ]

theorem cons_iff {I : Type} {k : ℕ} (ν : I → ℕ) (a : I) (t : Fin k → I) :
    (∀ i, (List.ofFn (Fin.cons a t : Fin (k+1) → I)).count i = ν i) ↔
      (1 ≤ ν a ∧ ∀ i, (List.ofFn t).count i = Function.update ν a (ν a - 1) i) := by
  simp only [ofFn_cons_count]
  constructor
  · intro h
    have ha := h a
    simp only [if_true] at ha
    refine ⟨by omega, fun i => ?_⟩
    by_cases hi : i = a
    · subst hi; simp only [Function.update_self]; omega
    · have := h i
      rw [if_neg (Ne.symm hi)] at this
      simp only [Function.update_apply, hi, if_false]; omega
  · rintro ⟨h1, h⟩ i
    by_cases hi : i = a
    · subst hi; have := h i; simp only [Function.update_self] at this; simp only [if_true]; omega
    · have := h i
      simp only [Function.update_apply, hi, if_false] at this
      rw [if_neg (Ne.symm hi)]; omega

theorem card_mul_prod_factorial : ∀ {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ), ∑ i, ν i = k →
    (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card *
      ∏ i, (ν i).factorial = k.factorial := by
  intro I _ k
  induction k with
  | zero =>
    intro ν hν
    have h0 : ∀ i, ν i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hν) i (Finset.mem_univ _)
    have : (Finset.univ.filter (fun s : Fin 0 → I => ∀ i, (List.ofFn s).count i = ν i)) = Finset.univ := by
      ext s; simp [h0]
    rw [this]; simp [h0]
  | succ k ih =>
    intro ν hν
    rw [Finset.card_filter, ← (Fin.consEquiv (fun _ : Fin (k+1) => I)).sum_comp, Fintype.sum_prod_type]
    have key : ∀ a : I, (∑ t : Fin k → I, if (∀ i, (List.ofFn (Fin.consEquiv (fun _ : Fin (k+1) => I) (a, t))).count i = ν i) then 1 else 0) *
        ∏ i, (ν i).factorial = ν a * k.factorial := by
      intro a
      have hc : ∀ t : Fin k → I, (∀ i, (List.ofFn (Fin.consEquiv (fun _ : Fin (k+1) => I) (a, t))).count i = ν i) ↔
          (1 ≤ ν a ∧ ∀ i, (List.ofFn t).count i = Function.update ν a (ν a - 1) i) := fun t => cons_iff ν a t
      simp_rw [hc]
      by_cases ha : 1 ≤ ν a
      · simp only [ha, true_and]
        rw [← Finset.card_filter]
        set μ := Function.update ν a (ν a - 1) with hμ
        have hs1 : ∑ i, μ i = (ν a - 1) + ∑ i ∈ Finset.univ \ {a}, ν i := by
          rw [hμ, Finset.sum_update_of_mem (Finset.mem_univ a)]
        have hs2 : ∑ i, ν i = ν a + ∑ i ∈ Finset.univ \ {a}, ν i :=
          Fintype.sum_eq_add_sum_compl a _
        have hμs : ∑ i, μ i = k := by omega
        have h1 : ∏ i, (μ i).factorial = (ν a - 1).factorial * ∏ i ∈ Finset.univ \ {a}, (ν i).factorial := by
          rw [Fintype.prod_eq_mul_prod_compl a]
          congr 1
          · simp [hμ]
          · apply Finset.prod_congr rfl
            intro i hi
            simp only [Finset.mem_compl, Finset.mem_singleton] at hi
            simp [hμ, Function.update_apply, hi]
        have h2 : ∏ i, (ν i).factorial = (ν a).factorial * ∏ i ∈ Finset.univ \ {a}, (ν i).factorial :=
          Fintype.prod_eq_mul_prod_compl a _
        have h3 : (ν a).factorial = ν a * (ν a - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
        have hi := ih μ hμs
        rw [h1] at hi
        rw [h2, h3, ← hi]
        ring
      · have : ν a = 0 := by omega
        simp [ha, this]
    rw [Finset.sum_mul]
    simp_rw [key]
    rw [← Finset.sum_mul, hν, Nat.factorial_succ]

end GlobalTheory.MultinomialCount
end

open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_multiset_words_mul_factorial : ∀ {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ), ∑ i, ν i = k → (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card * ∏ i, (ν i).factorial = k.factorial := by
  atlas_forward_decl GlobalTheory.MultinomialCount.card_mul_prod_factorial
end

section
section
open GlobalTheory.LatJet
open scoped Classical

namespace GlobalTheory.JetMul

theorem finite_jet_index {I : Type} [Fintype I] {n : ℕ} : Finite (Idx I n) := by
  refine Finite.of_injective (fun ν : Idx I n => fun i => (⟨ν.1 i, ?_⟩ : Fin (n + 2))) ?_
  · have h1 : ν.1 i ≤ ∑ j, ν.1 j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 := ν.2
    omega
  · intro a b h
    apply Subtype.ext
    funext i
    have := congrFun h i
    simpa using congrArg Fin.val this

theorem reprMul {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B)
    (hx : ∀ ν : Idx I n, J.b.repr x ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F)
    (hy : ∀ ν : Idx I n, J.b.repr y ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G)
    (μ : Idx I n) :
    J.b.repr (x * y) μ = ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm μ.1) (F * G) := by
  haveI : Finite (Idx I n) := finite_jet_index
  haveI : Fintype (Idx I n) := Fintype.ofFinite _
  have hb : ∀ ν ν' : Idx I n, J.b.repr (J.b ν * J.b ν') μ =
      if ν.1 + ν'.1 = μ.1 then ((∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i) : ℕ) : ℂ) else 0 := by
    intro ν ν'
    rw [J.mul]
    split_ifs with h1 h2 h2
    · rw [map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, if_pos (Subtype.ext h2)]
      simp [nsmul_eq_mul]
    · rw [map_nsmul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply, if_neg (fun h => h2 (congrArg Subtype.val h))]
      simp
    · exact absurd (by rw [h2]; exact μ.2) h1
    · simp
  have hxy : x * y = ∑ ν, ∑ ν', (J.b.repr x ν * J.b.repr y ν') • (J.b ν * J.b ν') := by
    conv_lhs => rw [← J.b.sum_repr x, ← J.b.sum_repr y]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν' _ => ?_
    rw [smul_mul_smul_comm]
  rw [hxy, map_sum, Finsupp.finset_sum_apply]
  simp_rw [map_sum, Finsupp.finset_sum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul, hb, hx, hy]
  have hfac : ∀ ν ν' : Idx I n, ν.1 + ν'.1 = μ.1 →
      (∏ i, (ν.1 i).factorial) * (∏ i, (ν'.1 i).factorial) * (∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i)) =
        ∏ i, (μ.1 i).factorial := by
    intro ν ν' h
    rw [← h, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Pi.add_apply, ← Nat.add_choose_mul_factorial_mul_factorial (ν.1 i) (ν'.1 i), Nat.choose_symm_add]
    ring
  have hterm : ∀ ν ν' : Idx I n,
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F *
        (((∏ i, (ν'.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G) *
        (if ν.1 + ν'.1 = μ.1 then ((∏ i, (ν.1 i + ν'.1 i).choose (ν.1 i) : ℕ) : ℂ) else 0) =
      if ν.1 + ν'.1 = μ.1 then ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) *
        (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G)
      else 0 := by
    intro ν ν'
    split_ifs with h
    · rw [← hfac ν ν' h]
      push_cast
      ring
    · simp
  simp_rw [hterm]
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_product' (f := fun ν ν' : Idx I n => if ν.1 + ν'.1 = μ.1 then ((∏ i, (μ.1 i).factorial : ℕ) : ℂ) *
        (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν'.1) G)
      else 0), ← Finset.sum_filter]
  have hle : ∀ p : (I →₀ ℕ) × (I →₀ ℕ), p ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.equivFunOnFinite.symm μ.1) →
      (∑ i, p.1 i ≤ n + 1) ∧ (∑ i, p.2 i ≤ n + 1) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hμ := μ.2
    have e : ∀ i, p.1 i + p.2 i = μ.1 i := fun i => by
      have := DFunLike.congr_fun hp i
      simpa using this
    have s : ∑ i, p.1 i + ∑ i, p.2 i = ∑ i, μ.1 i := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => e i
    omega
  refine Finset.sum_bij' (fun a _ => (Finsupp.equivFunOnFinite.symm a.1.1, Finsupp.equivFunOnFinite.symm a.2.1))
    (fun p hp => (⟨p.1, (hle p hp).1⟩, ⟨p.2, (hle p hp).2⟩)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    ext i
    simp [← ha.2]
  · intro p hp
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    funext i
    have := DFunLike.congr_fun hp i
    simpa using this
  · intro a ha
    rfl
  · intro p hp
    ext i <;> simp
  · intro a ha
    rw [Finset.mem_filter] at ha

end GlobalTheory.JetMul
end

open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_repr_mul_power_series : ∀ {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B), (∀ ν : Idx I n, J.b.repr x ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F) → (∀ ν : Idx I n, J.b.repr y ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G) → ∀ ν : Idx I n, J.b.repr (x * y) ν = ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (F * G) := by
  atlas_forward_decl GlobalTheory.JetMul.reprMul
end

section
section
set_option autoImplicit false
noncomputable section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical

namespace GlobalTheory.JetCalcPf

theorem prod_t_list {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hc : ∑ i, l.count i ≤ n + 1) :
    (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ :=
  GlobalTheory.T.jet_ring_prod_eq_factorial_smul J l hc

theorem prod_t_list_eq_zero {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I)
    (hl : n + 1 < l.length) : (l.map J.t).prod = 0 :=
  GlobalTheory.T.jet_ring_prod_eq_zero_of_long J l hl

theorem card_count_mul {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ) (hν : ∑ i, ν i = k) :
    (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card * ∏ i, (ν i).factorial
      = k.factorial :=
  GlobalTheory.T.card_multiset_words_mul_factorial k ν hν

theorem repr_mul_of_coeff {I : Type} [Fintype I] {n : ℕ} (J : JetRing ℂ I n) (F G : MvPowerSeries I ℂ) (x y : J.B)
    (hx : ∀ ν : Idx I n, J.b.repr x ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) F)
    (hy : ∀ ν : Idx I n, J.b.repr y ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) G)
    (ν : Idx I n) : J.b.repr (x * y) ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (F * G) :=
  GlobalTheory.T.jet_ring_repr_mul_power_series J F G x y hx hy ν

theorem iterD_eq {I : Type} [Fintype I] (l : List I) (g : (I → ℂ) → ℂ) :
    iterD l g = GlobalTheory.lineDerivList ℂ (l.map fun i => (Pi.single i 1 : I → ℂ)) g := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [iterD, List.foldr_cons, List.map_cons, GlobalTheory.lineDerivList_cons] at ih ⊢; rw [← ih]; rfl

end GlobalTheory.JetCalcPf

namespace GlobalTheory.JetCalcPf

variable {I : Type} [Fintype I] {n : ℕ}

theorem sum_count (l : List I) : ∑ i, l.count i = l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.length_cons, beq_iff_eq]
    simp

theorem repr_prod_t_eq_ite_factorial (J : JetRing ℂ I n) (ν : Idx I n) {k : ℕ} (s : Fin k → I) :
    J.b.repr (∏ a, J.t (s a)) ν =
      if (∀ i, (List.ofFn s).count i = ν.1 i) then ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0 := by
  have e : ∏ a, J.t (s a) = ((List.ofFn s).map J.t).prod := by
    rw [List.map_ofFn, List.prod_ofFn]; rfl
  rw [e]
  by_cases hk : k ≤ n + 1
  · have hc : ∑ i, (List.ofFn s).count i ≤ n + 1 := by rw [sum_count, List.length_ofFn]; exact hk
    rw [prod_t_list J _ hc, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hP : ∀ i, (List.ofFn s).count i = ν.1 i
    · have hν : (⟨fun i => (List.ofFn s).count i, hc⟩ : Idx I n) = ν := Subtype.ext (funext hP)
      rw [if_pos hν, if_pos hP, smul_eq_mul, mul_one]
      simp only [hP]
    · rw [if_neg hP, if_neg]
      · simp
      · intro h; exact hP fun i => congrFun (congrArg Subtype.val h) i
  · rw [prod_t_list_eq_zero J _ (by rw [List.length_ofFn]; omega), map_zero, Finsupp.zero_apply, if_neg]
    intro hP
    have h1 := ν.2
    have h2 : ∑ i, ν.1 i = k := by simp only [← hP]; rw [sum_count, List.length_ofFn]
    omega

theorem iFD_eq_iterD {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) {k : ℕ} (s : Fin k → I) (u : List I)
    (h : ∀ i, (List.ofFn s).count i = u.count i) :
    iteratedFDeriv ℂ k f 0 (fun a => (Pi.single (s a) 1 : I → ℂ)) = iterD u f 0 := by
  rw [iterD_eq, ← GlobalTheory.lineDerivList_ofFn hf]
  have hp : (List.ofFn s).Perm u := List.perm_iff_count.2 fun i => h i
  have e : List.ofFn (fun a => (Pi.single (s a) 1 : I → ℂ)) = (List.ofFn s).map fun i => (Pi.single i 1 : I → ℂ) := by
    rw [List.map_ofFn]; rfl
  rw [e]
  exact GlobalTheory.lineDerivList_perm hf (hp.map _)

theorem coeff_jet (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (ν : Idx I n) (u : List I)
    (hu : ∀ i, u.count i = ν.1 i) : J.b.repr (jet J f) ν = iterD u f 0 := by
  set K := ∑ i, ν.1 i with hK
  have hKn : K ≤ n + 1 := ν.2
  simp only [jet, GlobalTheory.PeriodFamily.taylor, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, repr_prod_t_eq_ite_factorial]
  rw [Finset.sum_eq_single_of_mem K (Finset.mem_range.2 (by omega))]
  · have step : ∀ s : Fin K → I, ((K.factorial : ℂ)⁻¹ * iteratedFDeriv ℂ K f 0 (fun a => (Pi.single (s a) 1 : I → ℂ))) *
        (if (∀ i, (List.ofFn s).count i = ν.1 i) then ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0) =
        if (∀ i, (List.ofFn s).count i = ν.1 i) then
          (K.factorial : ℂ)⁻¹ * iterD u f 0 * ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) else 0 := by
      intro s
      split_ifs with hP
      · rw [iFD_eq_iterD hf s u fun i => (hP i).trans (hu i).symm]
      · rw [mul_zero]
    simp only [step]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hc := card_count_mul K ν.1 rfl
    have hc' : ((Finset.univ.filter (fun s : Fin K → I => ∀ i, (List.ofFn s).count i = ν.1 i)).card : ℂ) *
        ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) = (K.factorial : ℂ) := by exact_mod_cast hc
    have hK0 : (K.factorial : ℂ) ≠ 0 := by exact_mod_cast K.factorial_ne_zero
    calc _ = ((Finset.univ.filter (fun s : Fin K → I => ∀ i, (List.ofFn s).count i = ν.1 i)).card : ℂ) *
        ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * (K.factorial : ℂ)⁻¹ * iterD u f 0 := by ring
      _ = _ := by rw [hc', mul_inv_cancel₀ hK0, one_mul]
  · intro k _ hk
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [if_neg, mul_zero]
    intro hP
    apply hk
    have := sum_count (List.ofFn s)
    rw [List.length_ofFn] at this
    rw [← this, hK]; simp only [hP]

theorem repr_jet_eq_coeff (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (ν : Idx I n) :
    J.b.repr (jet J f) ν =
      ((∏ i, (ν.1 i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm ν.1) (GlobalTheory.taylor f) := by
  set m : I →₀ ℕ := Finsupp.equivFunOnFinite.symm ν.1 with hm
  have hmi : ∀ i, m i = ν.1 i := fun i => by simp [hm]
  set l := (Finsupp.toMultiset m).toList
  have hl : (l : Multiset I) = Finsupp.toMultiset m := Multiset.coe_toList _
  have hcount : ∀ i, l.count i = ν.1 i := fun i => by
    rw [← hmi, ← Finsupp.count_toMultiset, ← hl, Multiset.coe_count]
  rw [GlobalTheory.taylor_eq_taylorDir, GlobalTheory.coeff_taylorDir_eq_lineDerivList _ hf hl, ← iterD_eq, ← coeff_jet J hf ν l hcount]
  have h0 : ((∏ i, (m i).factorial : ℕ) : ℂ) ≠ 0 := GlobalTheory.cast_prod_factorial_ne_zero m
  simp only [hmi] at h0 ⊢
  rw [mul_inv_cancel_left₀ h0]

theorem jetCalc : JetCalc := by
  intro I _ n J
  refine ⟨fun f hf ν u hu => coeff_jet J hf ν u hu, fun f g hf hg => ⟨?_, ?_⟩, fun f g h => ?_, fun a => ?_,
    fun i => ?_, fun i => ?_, fun s => ?_⟩
  · refine J.b.ext_elem fun ν => ?_
    rw [repr_mul_of_coeff J _ _ _ _ (repr_jet_eq_coeff J hf) (repr_jet_eq_coeff J hg) ν,
      repr_jet_eq_coeff J (hf.mul hg), GlobalTheory.taylor_mul hf hg]
  · refine J.b.ext_elem fun ν => ?_
    rw [map_add, Finsupp.add_apply, repr_jet_eq_coeff J hf, repr_jet_eq_coeff J hg,
      repr_jet_eq_coeff J (hf.add hg), GlobalTheory.taylor_add hf hg, map_add, mul_add]
  · have e : ∀ k, iteratedFDeriv ℂ k f 0 = iteratedFDeriv ℂ k g 0 := fun k => (h.iteratedFDeriv ℂ k).eq_of_nhds
    simp only [jet, GlobalTheory.PeriodFamily.taylor, e]
  · refine J.b.ext_elem fun ν => ?_
    rw [repr_jet_eq_coeff J analyticAt_const, GlobalTheory.taylor_const, MvPowerSeries.coeff_C,
      Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    by_cases hν : ν = ⟨0, by simp⟩
    · subst hν
      have h0 : Finsupp.equivFunOnFinite.symm (0 : I → ℕ) = 0 := by ext; simp
      simp [h0]
    · rw [if_neg (Ne.symm hν), if_neg, mul_zero, smul_zero]
      intro h; apply hν; apply Subtype.ext; funext i
      have := congrArg (fun m : I →₀ ℕ => m i) h
      simpa using this
  · have ha : AnalyticAt ℂ (fun z : I → ℂ => z i) 0 :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt 0
    refine J.b.ext_elem fun ν => ?_
    rw [repr_jet_eq_coeff J ha, GlobalTheory.taylor_coord, MvPowerSeries.coeff_X, JetRing.t, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases hν : ν.1 = Pi.single i 1
    · have h1 : (⟨Pi.single i 1, by simp⟩ : Idx I n) = ν := Subtype.ext hν.symm
      have h2 : Finsupp.equivFunOnFinite.symm ν.1 = Finsupp.single i 1 := by
        ext j; simp [hν, Pi.single_apply, Finsupp.single_apply, eq_comm]
      rw [if_pos h1, if_pos h2, hν, mul_one]
      have : ∀ j, (Pi.single i 1 : I → ℕ) j = 0 ∨ (Pi.single i 1 : I → ℕ) j = 1 := fun j => by
        by_cases hj : j = i <;> simp [hj]
      simp only [Nat.cast_eq_one]
      exact Finset.prod_eq_one fun j _ => by rcases this j with h | h <;> rw [h] <;> rfl
    · have h1 : (⟨Pi.single i 1, by simp⟩ : Idx I n) ≠ ν := fun h => hν (congrArg Subtype.val h).symm
      have h2 : Finsupp.equivFunOnFinite.symm ν.1 ≠ Finsupp.single i 1 := fun h => hν (by
        funext j; have := congrArg (fun m : I →₀ ℕ => m j) h; simpa [Pi.single_apply, Finsupp.single_apply, eq_comm] using this)
      rw [if_neg h1, if_neg h2, mul_zero]
  · rw [J.π_eq, JetRing.t, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
    intro h
    have := congrFun (congrArg Subtype.val h) i
    simp at this
  · have e : ∏ a, J.t (s a) = ((List.ofFn s).map J.t).prod := by
      rw [List.map_ofFn, List.prod_ofFn]; rfl
    rw [e, prod_t_list_eq_zero J _ (by rw [List.length_ofFn]; omega)]

end GlobalTheory.JetCalcPf
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_calculus_statement : JetCalc := by
  atlas_forward_decl GlobalTheory.JetCalcPf.jetCalc
end

section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_determinant_of_de_rham : GlobalTheory.Published.AbelianDeRham → JetCalc → JetDet := by
  first | exact @GlobalTheory.LatJet.An.Det.jetDet | exact GlobalTheory.LatJet.An.Det.jetDet | (intros; apply GlobalTheory.LatJet.An.Det.jetDet <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_appell_humbert_uniformization : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → ∀ u : HolUnif X.A (X.diag c) (Module.finrank ℚ F),
    ∃ (u' : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ)
      (χ : u'.Λ → ℂ), u'.ex = u.ex ∧ u'.IsAH Hm χ := by
  first | exact @GlobalTheory.RealMult.Obj.exists_isAH_diag | exact GlobalTheory.RealMult.Obj.exists_isAH_diag | (intros; apply GlobalTheory.RealMult.Obj.exists_isAH_diag <;> assumption)
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.appell_humbert_real_multiplication : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt),
    IsTotPos (c : F) → ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) → (F →+* ℂ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ e j (a : F) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (Hm : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ →
    ∀ (a : 𝓞 F) i j, e i (a : F) * Hm i j = Hm i j * starRingEnd ℂ (e j (a : F)) := by
  first | exact @GlobalTheory.RosatiAH.rosati_diag | exact GlobalTheory.RosatiAH.rosati_diag | (intros; apply GlobalTheory.RosatiAH.rosati_diag <;> assumption)
end

section
section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DiagAH

theorem conj_eq_of_totallyReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (φ : F →+* ℂ) (x : F) :
    starRingEnd ℂ (φ x) = φ x := by
  have h : ComplexEmbedding.IsReal φ :=
    (NumberField.InfinitePlace.isReal_mk_iff).1 (IsTotallyReal.isReal _)
  rw [← ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.isReal_iff.1 h]

theorem exists_int_ne {F : Type} [Field F] [NumberField F] {φ ψ : F →+* ℂ} (h : φ ≠ ψ) :
    ∃ a : 𝓞 F, φ (a : F) ≠ ψ (a : F) := by
  by_contra hall
  push_neg at hall
  exact h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun a ↦ hall a))

theorem eq_diagonal_of_comm {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) ℂ) (hH : Hm.IsHermitian) (e : Fin n → (F →+* ℂ)) (he : Function.Injective e)
    (h : ∀ (a : 𝓞 F) i j, e i (a : F) * Hm i j = Hm i j * starRingEnd ℂ (e j (a : F))) :
    Hm = Matrix.diagonal fun j ↦ ((Hm j j).re : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    have := congrFun (congrFun hH i) i
    simp only [Matrix.conjTranspose_apply] at this
    exact (Complex.conj_eq_iff_re.1 this).symm
  · rw [Matrix.diagonal_apply_ne _ hij]
    obtain ⟨a, ha⟩ := exists_int_ne (he.ne hij)
    have h1 := h a i j
    rw [conj_eq_of_totallyReal] at h1
    have h2 : (e i (a : F) - e j (a : F)) * Hm i j = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)

theorem diagFrame : DiagFrame := by
  intro F _ _ _ 𝔠 X c hc u e he hact
  obtain ⟨u', Hm, χ, hex, hAH⟩ := GlobalTheory.T.exists_appell_humbert_uniformization F 𝔠 X c hc u
  have hact' : ∀ (a : 𝓞 F) w, u'.ex (fun j ↦ e j (a : F) * w j) = u'.ex w ≫ X.rm.act a := by
    rw [hex]; exact hact
  have hsym := GlobalTheory.T.appell_humbert_real_multiplication F 𝔠 X c hc u' e hact' Hm χ hAH
  have hdiag := eq_diagonal_of_comm Hm hAH.1 e he hsym
  refine ⟨u', fun j ↦ (Hm j j).re, hex, χ, ?_⟩
  rw [← hdiag]
  exact hAH

end GlobalTheory.DiagAH
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_frame_statement : DiagFrame := by
  atlas_forward_decl GlobalTheory.DiagAH.diagFrame
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

namespace GlobalTheory.LatJet.An

theorem germEx_of_chart_holLift : Chart → HolLift → GermEx := by
  intro hC hH E _ _ _ I _ 𝔠 φ c y _ _ n T J Y
  obtain ⟨B, _, _, hsm, X, δ, j, q, hpull⟩ := hC (FR E) 𝔠 I n J Y.X'
  obtain ⟨δ'', hδ'', -⟩ := GlobalTheory.RealMult.Obj.IsPullBy.existsUnique_detGen (j : B →+* J.B) hpull δ
  have hmem : Y.δ'.1 ∈ Submodule.span J.B {δ''.1} := by
    rw [δ''.2]; exact Submodule.mem_top
  obtain ⟨e, he⟩ := Submodule.mem_span_singleton.1 hmem
  obtain ⟨U, yy, hU, h0, hhol, hjet⟩ := hH B I n J j
  exact ⟨{
    B := B
    smooth := hsm
    X := X
    δ := δ
    j := j
    q := q
    pull := hpull
    δ'' := δ''
    corr := hδ''
    e := e
    he := he.symm
    U := U
    isOpen := hU
    zero := h0
    y := yy
    hol := hhol
    jet_eq := hjet }⟩

end GlobalTheory.LatJet.An
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_existence_of_chart : Chart → HolLift → GermEx := by
  atlas_forward_decl GlobalTheory.LatJet.An.germEx_of_chart_holLift
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.LatJet GlobalTheory.LatJet.An GlobalTheory.LatJet.An.Det
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An.ZetaNonvanishing₂

theorem mem_Fil_iff {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (H : LieExact A) {x : HdR A}
    {w : Fin g → ℂ} (h : ∃ v, IsLieImage x v ∧ u.IsDiff w v) : x ∈ Fil A ↔ w = 0 := by
  obtain ⟨v, h1, h2⟩ := h
  refine ⟨fun hx ↦ ?_, fun hw ↦ ?_⟩
  · obtain rfl : v = 1 := (H.1 x).unique h1 (isLieImage_one_iff.2 hx)
    exact ArchMetricCompare.eq_zero_of_isDiff u h2
  · obtain rfl : v = 1 := (ArchMetricCompare.isDiff_ne_iff u h1.1 h2).1 hw
    exact isLieImage_one_iff.1 h1

theorem vec_unique {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (H : LieExact A) {x : HdR A}
    {w w' : Fin g → ℂ} (h : ∃ v, IsLieImage x v ∧ u.IsDiff w v) (h' : ∃ v, IsLieImage x v ∧ u.IsDiff w' v) : w = w' := by
  have key := exists_lie_comb u (fun _ : Bool ↦ x) (fun b ↦ if b then w else w') (fun b ↦ by cases b <;> simpa)
    (Finsupp.single true 1 - Finsupp.single false 1)
  simp only [map_sub, Finsupp.linearCombination_single, one_smul, sub_self, if_true, Bool.false_eq_true, if_false] at key
  exact sub_eq_zero.1 ((mem_Fil_iff u H key).1 (zero_mem _))

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ}

theorem pair_special {L : Set E} (T : CxPt 𝔠 φ L) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P)
    (c d : T.U.u.Λ →₀ ℂ) : T.ψ (Finsupp.linearCombination ℂ P c) (Finsupp.linearCombination ℂ P d) =
      ((ε : ℤ) : ℂ) * Real.pi * ∑ a, T.U.h (T.U.e a) * (hol _ c a * ahol _ d a - ahol _ c a * hol _ d a) := by
  obtain ⟨χ, hχ⟩ := T.U.ah
  rw [pair_comb _ P T.ψ (fun a ↦ T.U.h (T.U.e a)) _ (hP.2.2.2.2 _ χ T.ψ hχ T.pol) c d]
  congr 1
  field_simp

theorem exists_comb_eigen [IsCMField E] (H : GlobalTheory.Published.AbelianDeRham) (hφ : IsCMType φ) {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {y : (Af E)ˣ} (T : CxPt 𝔠 φ (lattice c y)) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P) (i : I) :
    ∃ d, Finsupp.linearCombination ℂ P d = T.y i ∧ hol _ d = Pi.single (T.U.e.symm i) (T.w i) ∧ ahol _ d = 0 := by
  obtain ⟨d, hd⟩ : T.y i ∈ LinearMap.range (Finsupp.linearCombination ℂ P) := by
    rw [Finsupp.range_linearCombination, hP.1]; trivial
  refine ⟨d, hd, vec_unique T.U.u (H.2.1 ℂ T.X.A _ T.X.ab T.X.dim).1 (hd ▸ exists_lie_comb T.U.u P _ hP.2.2.1 d) (T.cm i).2,
    funext fun m ↦ ?_⟩
  obtain ⟨a, h1, h2⟩ := exists_comb _ T.U.u.full (Pi.single m 1)
  have h0 : T.ψ (Finsupp.linearCombination ℂ P a) (T.y i) = 0 := by
    have e : (1 : ℂ) • (T.ψ (Finsupp.linearCombination ℂ P a) (T.y i) • T.y i) = 0 :=
      low_eq_zero hφ hc { T with s := fun _ ↦ 1 } hP h1 h2 i
    rw [one_smul] at e
    rcases smul_eq_zero.1 e with e | e
    · exact e
    · rw [e, map_zero]
  obtain ⟨χ, hχ⟩ := T.U.ah
  have hh : (T.U.h (T.U.e m) : ℂ) ≠ 0 := fun e ↦ by
    have := hχ.2.1 (Pi.single m 1) (by simp)
    simp [Matrix.mulVec_diagonal, e] at this
  rw [← hd, pair_special T hP] at h0
  simp only [h1, h2, Pi.zero_apply, zero_mul, sub_zero, Pi.single_apply, ite_mul, _root_.one_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h0
  simpa [hh, Real.pi_ne_zero] using h0

theorem low_anti [IsCMField E] (H : GlobalTheory.Published.AbelianDeRham) (hφ : IsCMType φ) {c : Ideal (OF E)} (hc : c ≠ ⊥)
    {y : (Af E)ˣ} (T : CxPt 𝔠 φ (lattice c y)) {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P) (i : I)
    {b : T.U.u.Λ →₀ ℂ} (h1 : hol _ b = 0) (h2 : ahol _ b = Pi.single (T.U.e.symm i) 1) :
    ∃ d, hol _ d = Pi.single (T.U.e.symm i) (-(((ε : ℤ) : ℂ) * T.A i)) ∧ ahol _ d = 0 ∧
      ∀ k, T.low k (Finsupp.linearCombination ℂ P b) = if k = i then Finsupp.linearCombination ℂ P d else 0 := by
  have key : ∀ k, T.low k (Finsupp.linearCombination ℂ P b) =
      (if k = i then -(((ε : ℤ) : ℂ) * Real.pi * T.U.h i * T.s i * T.w i) else 0) • T.y k := fun k ↦ by
    obtain ⟨d, e0, e1, e2⟩ := exists_comb_eigen H hφ hc T hP k
    have e := pair_special T hP b d
    rw [e0] at e
    change T.s k • (T.ψ _ (T.y k) • T.y k) = _
    rw [e, smul_smul]
    congr 1
    simp only [h1, h2, e1, Pi.zero_apply, zero_mul, zero_sub, Pi.single_apply, ite_mul, _root_.one_mul, mul_neg, mul_ite, mul_zero,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq]
    by_cases hk : k = i
    · subst hk
      simp only [if_true]
      ring
    · simp [hk, Ne.symm hk]
  obtain ⟨d, e0, e1, e2⟩ := exists_comb_eigen H hφ hc T hP i
  refine ⟨(-(((ε : ℤ) : ℂ) * Real.pi * T.U.h i * T.s i * T.w i)) • d, ?_, by rw [map_smul, e2, smul_zero], fun k ↦ ?_⟩
  · rw [map_smul, e1, ← Pi.single_smul, smul_eq_mul, CxPt.A]
    congr 1
    ring
  · rw [key]
    split_ifs with hk
    · rw [map_smul, e0, hk]
    · exact zero_smul _ _

theorem exists_comb_anti {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (w : Fin g → ℂ) :
    ∃ c, hol Λ c = 0 ∧ ahol Λ c = w := by
  obtain ⟨c, h1, h2⟩ := exists_comb Λ h (star w)
  have k : ∀ c : Λ →₀ ℂ, ∃ c', hol Λ c' = star (ahol Λ c) ∧ ahol Λ c' = star (hol Λ c) := fun c ↦ by
    induction c using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp, by simp⟩
    | add c d hc hd =>
      obtain ⟨c', e1, e2⟩ := hc
      obtain ⟨d', e3, e4⟩ := hd
      exact ⟨c' + d', by simp only [map_add, e1, e3, star_add], by simp only [map_add, e2, e4, star_add]⟩
    | single x r => exact ⟨Finsupp.single x (star r), by simp, by simp⟩
  obtain ⟨c', e1, e2⟩ := k c
  exact ⟨c', by rw [e1, h2, star_zero], by rw [e2, h1, star_star]⟩

theorem isUnit_jet (hC : JetCalc) {n : ℕ} (J : JetRing ℂ I n) {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    IsUnit (jet J f) := by
  have e : J.π (jet J f) = f 0 := by
    rw [J.π_eq]
    exact (hC I n J).1 f hf _ [] fun _ ↦ rfl
  have hm : jet J f - algebraMap ℂ J.B (f 0) ∈ RingHom.ker J.π := by
    rw [RingHom.mem_ker, map_sub, e, J.π_algebraMap, sub_self]
  obtain ⟨N, hN⟩ := J.nil.exists_dpow_eq_zero
  have hn : IsNilpotent (jet J f - algebraMap ℂ J.B (f 0)) :=
    ⟨N, by rw [← J.κ.factorial_mul_dpow_eq_pow hm, hN N le_rfl, mul_zero]⟩
  simpa using hn.isUnit_add_right_of_commute ((Ne.isUnit h0).map (algebraMap ℂ J.B)) (Commute.all _ _)

section Main

variable {n : ℕ} {L : Set E} {T : CxPt 𝔠 φ L} {J : JetRing ℂ I n} {Y : Family J T.X T.δ T.low} {G : Germ Y} {ε : ℤˣ}

def period (K : Coord ε G) (c : T.U.u.Λ →₀ ℂ) (ω : primDR G.X.A) (z : I → ℂ) : ℂ :=
  Finsupp.linearCombination ℂ (K.P z) c ((K.mor z).pull ω)

theorem mem_Fil_fibre (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) (c : T.U.u.Λ →₀ ℂ) :
    Finsupp.linearCombination ℂ (K.P z) c ∈ Fil (K.X z).A ↔ ∀ a, hol _ c a + K.ζ z (T.U.e a) * ahol _ c a = 0 := by
  rw [mem_Fil_iff (K.U z hz).u (H.2.1 ℂ (K.X z).A _ (K.X z).ab (K.X z).dim).1
    (exists_lie_comb (K.U z hz).u (K.P z) _ (K.lie z hz) c), funext_iff]
  refine forall_congr' fun a ↦ Eq.congr_left ?_
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
    RCLike.star_def, mul_add, Finset.sum_add_distrib, mul_left_comm _ (K.ζ z _), ← Finset.mul_sum]

theorem period_eq (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) {c d : T.U.u.Λ →₀ ℂ} {r : ℂ}
    (h : ∀ a, hol _ c a + K.ζ z (T.U.e a) * ahol _ c a = r * (hol _ d a + K.ζ z (T.U.e a) * ahol _ d a))
    {ω : primDR G.X.A} (hω : ω ∈ PrimitiveSubmodule G.X.A) : period K c ω z = r * period K d ω z := by
  have e := (mem_Fil_fibre H K hz (c - r • d)).2 fun a ↦ by
    simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h a
  have e' := (Submodule.mem_dualAnnihilator _).1 e ((K.mor z).pull ω) ((K.mor z).isMor.pullback1_mem_hodgeFiltration hω)
  rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at e'
  exact sub_eq_zero.1 e'

theorem exists_period_ne_zero (H : GlobalTheory.Published.AbelianDeRham) (K : Coord ε G) {z : I → ℂ} (hz : z ∈ K.V) {c : T.U.u.Λ →₀ ℂ}
    {a : Fin (Module.finrank ℚ (FR E))} (h : hol _ c a + K.ζ z (T.U.e a) * ahol _ c a ≠ 0) :
    ∃ ω ∈ PrimitiveSubmodule G.X.A, period K c ω z ≠ 0 := by
  by_contra hh
  push_neg at hh
  refine h ((mem_Fil_fibre H K hz c).1 ?_ a)
  letI : Algebra G.B ℂ := (G.y z : G.B →+* ℂ).toAlgebra
  have e := (H.2.2.1 G.B G.X.A _ G.X.ab G.X.dim ℂ (K.X z).A (K.q z) (K.pull z).grp).2
  refine (Submodule.mem_dualAnnihilator _).2 fun w hw ↦ ?_
  rw [e] at hw
  refine (Submodule.span_le (p := LinearMap.ker (Finsupp.linearCombination ℂ (K.P z) c))).2 ?_ hw
  rintro _ ⟨ω, hω, rfl⟩
  exact hh ω hω

theorem hasJet_period (hC : JetCalc) (K : Coord ε G) (hb : Y.mor.IsBC)
    (m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q)
    (c : T.U.u.Λ →₀ ℂ) (ω : primDR G.X.A) : HasJet J (period K c ω)
      (crysToDR J.κ Y.pull.grp (hb.bcMap (Finsupp.linearCombination ℂ K.P₀ c)) (m'.pull ω)) := by
  induction c using Finsupp.induction_linear with
  | zero =>
    have e : period K 0 ω = fun _ ↦ 0 := funext fun z ↦ by simp only [period, map_zero, LinearMap.zero_apply]
    simpa only [e, map_zero, LinearMap.zero_apply] using hasJet_const (J := J) 0
  | add c d hc hd =>
    have e : period K (c + d) ω = fun z ↦ period K c ω z + period K d ω z :=
      funext fun z ↦ by simp only [period, map_add, LinearMap.add_apply]
    simpa only [e, map_add, LinearMap.add_apply] using hc.add hC hd
  | single x r =>
    have e : period K (Finsupp.single x r) ω = fun z ↦ r * K.P z x ((K.mor z).pull ω) :=
      funext fun z ↦ by simp only [period, Finsupp.linearCombination_single, LinearMap.smul_apply, smul_eq_mul]
    rw [e, Finsupp.linearCombination_single, LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact (hasJet_const r).mul hC ⟨SCV.analyticAt_of_differentiableOn (K.P_hol x ω) (K.isOpen.mem_nhds K.zero),
      (K.horiz m' x _ (hb.corr_iff.2 rfl) ω).symm⟩

end Main

theorem jetZeta : GlobalTheory.Published.AbelianDeRham → JetCalc → JetZeta := by
  intro H hC
  refine ⟨1, ?_⟩
  intro ε E _ _ _ I _ 𝔠 φ c y hφ hc n T J Y G K i
  rw [_root_.one_mul]
  obtain ⟨a, a1, a2⟩ := exists_comb _ T.U.u.full (Pi.single (T.U.e.symm i) 1)
  obtain ⟨b, b1, b2⟩ := exists_comb_anti _ T.U.u.full (Pi.single (T.U.e.symm i) 1)
  obtain ⟨d, d1, d2, hd⟩ := low_anti H hφ hc T K.per i b1 b2
  have hV := K.isOpen.mem_nhds K.zero
  have m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) ((Category.comp_id _).trans (Category.id_comp _).symm) G.pull.grp
  have hb := isBC H T.X Y.mor
  obtain ⟨ω, hω, h0⟩ := exists_period_ne_zero H K K.zero (c := a) (a := T.U.e.symm i) (by simp [a1, a2])
  have hζ : AnalyticAt ℂ (fun z ↦ K.ζ z i) 0 := SCV.analyticAt_of_differentiableOn (differentiableOn_pi.1 K.ζ_hol i) hV
  have ja := hasJet_period hC K hb m' a ω
  have jb := hasJet_period hC K hb m' b ω
  have jd := hasJet_period hC K hb m' d ω
  have eb : period K b ω =ᶠ[𝓝 0] fun z ↦ K.ζ z i * period K a ω z := Filter.eventually_of_mem hV fun z hz ↦
    period_eq H K hz (fun m ↦ by
      by_cases hm : m = T.U.e.symm i
      · simp [a1, a2, b1, b2, hm]
      · simp [a1, a2, b1, b2, hm]) hω
  have ed : period K d ω =ᶠ[𝓝 0] fun z ↦ -(((ε : ℤ) : ℂ) * T.A i) * period K a ω z := Filter.eventually_of_mem hV fun z hz ↦
    period_eq H K hz (fun m ↦ by
      by_cases hm : m = T.U.e.symm i
      · simp [a1, a2, d1, d2, hm]
      · simp [a1, a2, d1, d2, hm]) hω
  have fb := jb.2.symm.trans ((Check.jet_congr J eb).trans (HasJet.mul hC ⟨hζ, rfl⟩ ⟨ja.1, rfl⟩).2)
  have fd := jd.2.symm.trans ((Check.jet_congr J ed).trans (HasJet.mul hC (hasJet_const _) ⟨ja.1, rfl⟩).2)
  have hF : Finsupp.linearCombination ℂ K.P₀ b ∈ Fil T.X.A :=
    (mem_Fil_iff T.U.u (H.2.1 ℂ T.X.A _ T.X.ab T.X.dim).1 (exists_lie_comb T.U.u K.P₀ _ K.per.2.2.1 b)).2 b1
  have hJ : IsJetElt J T.X T.low Y.mor (Finsupp.linearCombination ℂ K.P₀ b)
      (hb.bcMap (Finsupp.linearCombination ℂ K.P₀ b) + J.t i • hb.bcMap (Finsupp.linearCombination ℂ K.P₀ d)) := fun cc ↦ by
    rw [LinearMap.add_apply, LinearMap.smul_apply, hb.corr_iff.2 rfl cc, hb.corr_iff.2 rfl cc, Finset.sum_eq_single i, hd,
      if_pos rfl, smul_eq_mul]
    · intro k _ hk
      rw [hd, if_neg hk, LinearMap.zero_apply, map_zero, mul_zero]
    · exact fun h ↦ (h (Finset.mem_univ i)).elim
  have hz := (Submodule.mem_dualAnnihilator _).1 (Y.fil _ hF _ hJ) (m'.pull ω) (m'.isMor.pullback1_mem_hodgeFiltration hω)
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, fb, fd, smul_eq_mul, map_neg] at hz
  refine (isUnit_jet hC J ja.1 h0).mul_right_cancel ?_
  rw [Algebra.smul_def]
  linear_combination hz

end GlobalTheory.LatJet.An.ZetaNonvanishing₂
end
end

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_zeta_of_de_rham : GlobalTheory.Published.AbelianDeRham → JetCalc → JetZeta := by
  atlas_forward_decl GlobalTheory.LatJet.An.ZetaNonvanishing₂.jetZeta
end

section
section
set_option autoImplicit false

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

namespace GlobalTheory.LatJet.An

theorem jetAnalytic_of_periods :
    GlobalTheory.Published.GaussManinPeriods → GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.HilbertBlumenthal →
      GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
      GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetAnalytic :=
  fun hGM _ hHB _ hDR _ hS =>
    have hC : JetCalc := GlobalTheory.T.jet_calculus_statement
    jetAnalytic_of_steps hC (Chain.jetChain_of_jetCalc hC)
      (GlobalTheory.T.germ_existence_of_chart (GlobalTheory.T.chart_of_hilbert_blumenthal hHB) (holLift_of_jetCalc hC))
      (GlobalTheory.T.coordinate_existence_of_periods hGM hC GlobalTheory.T.diagonal_frame_statement) (GlobalTheory.T.jet_zeta_of_de_rham hDR hC) (GlobalTheory.T.jet_determinant_of_de_rham hDR hC) hS

end GlobalTheory.LatJet.An
end

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_analytic_of_periods : GlobalTheory.Published.GaussManinPeriods → GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.HilbertBlumenthal → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetAnalytic := by
  atlas_forward_decl GlobalTheory.LatJet.An.jetAnalytic_of_periods
end
