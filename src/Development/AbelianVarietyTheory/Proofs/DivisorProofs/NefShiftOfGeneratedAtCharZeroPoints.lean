import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroResidueField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleNsmul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField

section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo

set_option autoImplicit false

namespace GlobalTheory.TrueGeo.InducedGen

theorem exists_isGenerated_pow : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A.Induced M L q cf → Y.ample A.D → ∃ m : ℕ, 1 ≤ m ∧ GlobalTheory.IsGenerated ((L.pow m).B.pull M.j) := by
  intro F _ _ C Y A M L q cf hI hA
  obtain ⟨_, r, hr, _, _⟩ := hI
  have hq : Y.ample ((q : ℕ) • A.D) := Var.ample_nsmul F Y A.D q q.pos hA
  have hiso : LBIso (L.B.pull M.j) (toLB ((q : ℕ) • A.D)) := hr.lbIso (presents_toLB _)
  have hamp : IsAmpleLB (L.B.pull M.j) := IsAmpleLB.of_lbIso hq hr.isLB hiso
  obtain ⟨n, hn, hg⟩ := hamp.exists_isGenerated_pow
  refine ⟨n, hn, ?_⟩
  exact hg.of_lbIso (LB.isLB_pull (isLB_lbPow L.isLB n) M.j)
    (LBIso.symm (lbIso_lbPow_pull L.isLB M.j n))

end GlobalTheory.TrueGeo.InducedGen
end

section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_of_induced_bundle_generated : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L q cf → Y.ample A.D → ∃ m : ℕ, 1 ≤ m ∧ GlobalTheory.IsGenerated ((L.pow m).B.pull M.j) := by
  first | exact @GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow | exact GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow | (intros; apply GlobalTheory.TrueGeo.InducedGen.exists_isGenerated_pow <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ModelSecExt

open GlobalTheory.PrimSec GlobalTheory.AbLaw

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem genericPoint_mem_range (M : TrueGeo.Model Y) :
    haveI := M.ar.isIntegral; genericPoint M.X ∈ Set.range M.j := by
  haveI := M.ar.isIntegral
  have := M.ar.finite
  have := M.ar.isDomain
  haveI := HtSelfInter.charZero_residueField_genericPoint M.ar.charZero
  have h0 := Mean4O.asIdeal_eq_bot M.p (genericPoint M.X)
  have hr : genericPoint M.X ∈ Set.range (Limits.pullback.fst M.p (spMap (algebraMap (𝓞 F) F))) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext ?_⟩
    show Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, h0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
  obtain ⟨z, hz⟩ := hr
  refine ⟨M.pb.isoPullback.inv z, ?_⟩
  rw [← hz, ← M.pb.isoPullback_inv_fst, Scheme.Hom.comp_apply]

theorem app_injective (M : TrueGeo.Model Y) (W : M.X.Opens) : Function.Injective (M.j.app W).hom := by
  haveI := M.ar.isIntegral
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne
  obtain ⟨y, hy⟩ := genericPoint_mem_range M
  have hb : M.X.basicOpen a ≠ ⊥ := fun h => hne ((basicOpen_eq_bot_iff a).1 h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb
  have hη : genericPoint M.X ∈ M.X.basicOpen a := ((genericPoint_spec M.X).mem_open_set_iff (M.X.basicOpen a).isOpen).2 ⟨x, trivial, hx⟩
  have : y ∈ M.j ⁻¹ᵁ M.X.basicOpen a := by rw [Scheme.Hom.mem_preimage, hy]; exact hη
  rw [Scheme.preimage_basicOpen] at this
  change y ∈ Y.X.basicOpen ((M.j.app W).hom a) at this
  rw [ha, Scheme.basicOpen_zero] at this
  exact this

theorem exists_extension (M : TrueGeo.Model Y) {U : M.X.Opens} (t : Γ(Y.X, M.j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (V : M.X.Opens) (hV : V ≤ U) (b : Γ(M.X, V)), x ∈ V ∧
      (M.j.app V).hom b = rs Y.X (pre_le M.j hV) t) :
    ∃ b : Γ(M.X, U), (M.j.app U).hom b = t := by
  choose V hV b hx hb using h
  have hc : U ≤ ⨆ x : U, V x.1 x.2 := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := M.X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hV x.1 x.2)) hc (fun x => b x.1 x.2) (fun x y => by
      apply app_injective M
      refine (app_rs M.j inf_le_left _).trans (Eq.trans ?_ (app_rs M.j inf_le_right _).symm)
      rw [hb, hb]
      exact (rs_rs _ _ _).trans (rs_rs _ _ _).symm)
  refine ⟨s, Y.X.sheaf.eq_of_locally_eq' (fun x : U => M.j ⁻¹ᵁ V x.1 x.2) (M.j ⁻¹ᵁ U)
    (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨M.j y, hy⟩, hx _ hy⟩
  · exact (app_rs M.j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))

end GlobalTheory.ModelSecExt

open GlobalTheory.PrimSec GlobalTheory.AbLaw GlobalTheory.ModelSecExt in

theorem GlobalTheory.ModelSecExt.main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (B : LB M.X),
    B.IsLB → ∀ t : (B.pull M.j).Sec, ∃ s : B.Sec, ∀ y : Y.X,
      M.j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  intro F _ _ Y M B hB t
  haveI := M.ar.isIntegral
  haveI := M.ar.isNoetherian
  have hx : ∀ x : M.X, ∃ (i : B.ι) (W : M.X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ B.U i := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, B.U i from hB.cover ▸ trivial)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      M.X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
    exact ⟨i, W, hW, hxW, hWU⟩
  choose ci Wx hWa hxW hWle using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (Wx x : Set M.X)) (fun x => (Wx x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  choose π b hπ hb using fun x => exists_numerator M.pb (hWa x) (loc t (ci x) (hWle x))
  classical
  let c : 𝓞 F := ∏ x ∈ S, π x
  have hc : algebraMap (𝓞 F) F c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact Finset.prod_ne_zero_iff.2 fun x _ => hπ x
  have hb' : ∀ x ∈ S, ∃ b' : Γ(M.X, Wx x), (M.j.app (Wx x)).hom b' =
      cst Y.str (M.j ⁻¹ᵁ Wx x) (algebraMap (𝓞 F) F c) * loc t (ci x) (hWle x) := by
    intro x hxS
    refine ⟨cst M.p (Wx x) (∏ y ∈ S.erase x, π y) * b x, ?_⟩
    rw [map_mul, app_cst M.pb.w, hb, ← mul_assoc, ← map_mul, ← map_mul, Finset.prod_erase_mul _ _ hxS]
  choose! b' hb' using hb'
  have key : ∀ i, ∃ s : Γ(M.X, B.U i), (M.j.app (B.U i)).hom s =
      cst Y.str (M.j ⁻¹ᵁ B.U i) (algebraMap (𝓞 F) F c) * loc t i le_rfl := by
    intro i
    refine exists_extension M _ fun x hx => ?_
    obtain ⟨z, hzS, hxz⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    have hV : B.U i ⊓ Wx z ≤ B.U i := inf_le_left
    have hk : B.U i ⊓ Wx z ≤ B.U (ci z) := inf_le_right.trans (hWle z)
    refine ⟨B.U i ⊓ Wx z, hV, rs M.X (le_inf hV hk) (B.g i (ci z)).val * rs M.X inf_le_right (b' z), ⟨hx, hxz⟩, ?_⟩
    rw [map_mul, app_rs M.j (inf_le_right : B.U i ⊓ Wx z ≤ Wx z) (b' z), hb' z hzS, map_mul, rs_cst, rs_loc t (ci z) (hWle z) (inf_le_right : B.U i ⊓ Wx z ≤ Wx z), map_mul, rs_cst,
      rs_loc t i le_rfl hV,
      loc_trans t i (ci z) (le_rfl.trans hV) hk]
    ring
  choose s hs using key
  have hunit : ∀ W : Y.X.Opens, IsUnit (cst Y.str W (algebraMap (𝓞 F) F c)) := fun W =>
    (IsUnit.mk0 _ hc).map _
  refine ⟨⟨s, fun i k => ?_⟩, fun y => ?_⟩
  · apply app_injective M
    change (M.j.app _).hom (rs M.X inf_le_left (s i)) = (M.j.app _).hom (_ * rs M.X inf_le_right (s k))
    rw [map_mul, app_rs, app_rs, hs, hs, map_mul, map_mul, rs_cst, rs_cst,
      rs_loc t _ _ inf_le_left, rs_loc t _ _ inf_le_right, loc_trans t i k _ inf_le_right, rs_self]
    ring
  · have hmem : ∀ i, y ∈ M.j ⁻¹ᵁ B.U i →
        (M.j y ∈ M.X.basicOpen (s i) ↔ y ∈ Y.X.basicOpen (t.f (fun _ => i))) := by
      intro i hy
      change y ∈ M.j ⁻¹ᵁ M.X.basicOpen (s i) ↔ _
      rw [Scheme.preimage_basicOpen]
      change y ∈ Y.X.basicOpen ((M.j.app (B.U i)).hom (s i)) ↔ _
      rw [hs, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hunit _)]
      exact ⟨fun h => (mem_basicOpen_rs _ _ hy).1 h.2, fun h => ⟨hy, (mem_basicOpen_rs _ _ hy).2 h⟩⟩
    constructor
    · intro h
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ M.j ⁻¹ᵁ B.U i := M.X.basicOpen_le (s i) hi
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem i hy).1 hi⟩
    · intro h
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ M.j ⁻¹ᵁ B.U (k PUnit.unit) := Set.mem_iInter.1 (Y.X.basicOpen_le (t.f k) hk) PUnit.unit
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k PUnit.unit, (hmem (k PUnit.unit) hy).2 hk⟩
end
end

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_locus_section_pullback_extends : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (B : LB M.X), B.IsLB → ∀ t : (B.pull M.j).Sec, ∃ s : B.Sec, ∀ y : Y.X, M.j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  atlas_forward_decl GlobalTheory.ModelSecExt.main
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt

namespace GlobalTheory.AmpleHtLow

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem small_of_shift : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (L : HermLB p) (m : ℕ), 1 ≤ m → ∀ (s : (L.pow m).B.Sec), ∃ c : ℝ,
      s ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec := by
  intro k _ X p D hX L m hm s
  have := hX.finite_emb
  have hb : ∀ σ : k →+* ℂ, ∃ K : ℝ, ∀ y, ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y ≤ K := fun σ => by
    have := hX.compactSpace σ
    obtain ⟨K, hK⟩ := (isCompact_range (((L.pow m).cInf σ).continuous_nsq s)).bddAbove
    exact ⟨K, fun y => hK ⟨y, rfl⟩⟩
  choose K hK using hb
  have := Fintype.ofFinite (k →+* ℂ)
  have hK' : ∀ σ, K σ ≤ ∑ τ, |K τ| + 1 := fun σ => by
    have := Finset.single_le_sum (fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)) (Finset.mem_univ σ)
    linarith [le_abs_self (K σ)]
  have h1 : (1 : ℝ) ≤ ∑ τ, |K τ| + 1 := by
    linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => abs_nonneg (K τ)]
  set K' : ℝ := ∑ τ, |K τ| + 1
  have hl : 0 ≤ Real.log K' := Real.log_nonneg h1
  have hpos : 0 < K' := by linarith
  refine ⟨-(Real.log K' / 2), fun σ y => ?_⟩
  refine (le_of_eq (nsq_shift_pow L (fun _ => -(-(Real.log K' / 2))) (fun _ => rfl) m σ (CxPts.secVal p σ s) y)).trans ?_
  have h0 : 0 ≤ ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y := by unfold Weight.nsq; positivity
  have h2 : Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2)))) ≤ K'⁻¹ := by
    rw [show -(2 * (m : ℝ) * -(-(Real.log K' / 2))) = -((m : ℝ) * Real.log K') by ring,
      ← Real.exp_log hpos, ← Real.exp_neg, Real.exp_log hpos]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  calc ((L.pow m).φ σ).nsq (CxPts.secVal p σ s) y * Real.exp (-(2 * (m : ℝ) * -(-(Real.log K' / 2))))
      ≤ K' * K'⁻¹ := mul_le_mul ((hK σ y).trans (hK' σ)) h2 (Real.exp_pos _).le hpos.le
    _ = 1 := mul_inv_cancel₀ hpos.ne'

theorem htLow (hE : GlobalTheory.Published.ArExists) (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (hI : A.Induced M L q 0) (hA : Y.ample A.D) :
    ∃ C : ℝ, ∀ x : Y.X, IsClosed ({x} : Set Y.X) → -C ≤ A.ht x := by
  have := M.ar.isIntegral
  obtain ⟨m, hm, N, t, ht⟩ := GlobalTheory.T.power_of_induced_bundle_generated F (cxSt F) Y A M L q 0 hI hA
  have hs : ∀ i, ∃ s : (L.pow m).B.Sec, ∀ y : Y.X,
      M.j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t i) :=
    fun i => GlobalTheory.T.nonzero_locus_section_pullback_extends F Y M _ (L.pow m).isLB (t i)
  choose s hs using hs
  have hc : ∀ i, ∃ c : ℝ, s i ∈ ((L.shift (fun _ => -c) fun _ => rfl).pow m).smallSec :=
    fun i => small_of_shift (𝓞 F) M.X M.p Y.dim M.ar L m hm (s i)
  choose c hc using hc
  obtain ⟨h, H⟩ := (hE _ M.X M.p _ M.ar).1 L
  have hk : (0 : ℝ) < ((q : ℕ) : ℝ) * (A.n : ℕ) := mul_pos (Nat.cast_pos.2 q.pos) (Nat.cast_pos.2 A.n.pos)
  refine ⟨(∑ i, |c i|) / (((q : ℕ) : ℝ) * (A.n : ℕ)), fun x hx => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (t i) :=
    TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ x))
  have hN : (0 : ℝ) < Nat.card (M.X.residueField (M.j x) →+* ℂ) :=
    Nat.cast_pos.2 (NefModel.card_pos M hx)
  have hb : IsPtHt L (M.j x) (h (M.j x) / Nat.card (M.X.residueField (M.j x) →+* ℂ)) :=
    ⟨h, H, (div_mul_cancel₀ _ hN.ne').symm⟩
  have h1 := GlobalTheory.SmallSecHeight.le_ptHt (𝓞 F) M.X M.p Y.dim M.ar L m (c i) _ (M.j x) (s i) hm (hc i)
    ((hs i x).2 hi) (ClosedAlg.isAlgPt_of_isClosed F Y M x hx) hb
  rw [HtModel.ht_eq F _ Y A M L q hI x _ hx hb]
  have h2 : -(∑ j, |c j|) ≤ c i :=
    (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))).trans (neg_abs_le _)
  rw [← neg_div]
  exact div_le_div_of_nonneg_right (h2.trans h1) hk.le

theorem main : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp, ∃ C : ℝ,
    ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) → -C ≤ (O.met.ab c).ht b := by
  intro hP _ D O hO c
  obtain ⟨x, P, h⟩ := hO
  obtain ⟨M, L, q, hI, -⟩ := P.ab_model c
  rw [h.ab_eq]
  exact htLow hP.p4.arExists _ _ _ M L q hI (P.ab_ample c)

end GlobalTheory.AmpleHtLow

end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefOfGen

theorem card_pos_of_isAlgPt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {x : X} (hx : IsAlgPt x) : (0 : ℝ) < Nat.card (X.residueField x →+* ℂ) := by
  obtain ⟨hc, hd⟩ := hx
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint x
  have hr : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr] at hd
  have hbij : Function.Bijective (i.residueFieldMap (genericPoint Z)).hom := by
    refine ⟨RingHom.injective _, fun u => ?_⟩
    obtain ⟨u, rfl⟩ := Z.residue_surjective _ u
    obtain ⟨u, rfl⟩ := i.stalkMap_surjective _ u
    exact ⟨X.residue _ u, ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i _) u⟩
  have hc' : CharZero (Z.residueField (genericPoint Z)) := (RingHom.charZero_iff hbij.1).1 hc
  have hcΓ : CharZero Γ(Z, ⊤) := (Z.Γevaluation (genericPoint Z)).hom.charZero
  have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hcΓ hd
  have := GlobalTheory.SmallSecHeight.numberField hZ hc'
  rw [GlobalTheory.HtSelfInter.card_ringHom_eq]
  exact_mod_cast Nat.card_pos

theorem nef_of_gen : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (m N : ℕ) (s : Fin N → (M.pow m).B.Sec), 1 ≤ m → (∀ x : X, CharZero (X.residueField x) → ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.SemiPos D → NefFib M → ∃ t : ℝ, 0 ≤ t ∧ (M.shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hA k _ X _ p D hX M m N s hm hs hsp hf
  have hc : ∀ i, ∃ c : ℝ, s i ∈ ((M.shift (fun _ => -c) fun _ => rfl).pow m).smallSec :=
    fun i => GlobalTheory.AmpleHtLow.small_of_shift k X p D hX M m hm (s i)
  choose c hc using hc
  obtain ⟨h, H⟩ := (hA.arExists k X p D hX).1 M
  refine ⟨-(-(∑ i, |c i|)), ?_, GlobalTheory.HtSelfInter.isNef_shift hX hsp hf fun x hx => ?_⟩
  · rw [neg_neg]
    exact Finset.sum_nonneg fun j _ => abs_nonneg (c j)
  obtain ⟨i, hi⟩ := hs x hx.1
  have hN := card_pos_of_isAlgPt hX hx
  have hb : IsPtHt M x (h x / Nat.card (X.residueField x →+* ℂ)) :=
    ⟨h, H, (div_mul_cancel₀ _ hN.ne').symm⟩
  refine ⟨_, hb, ?_⟩
  have h1 := GlobalTheory.SmallSecHeight.le_ptHt k X p D hX M m (c i) _ x (s i) hm (hc i) hi hx hb
  have h2 : -(∑ j, |c j|) ≤ c i :=
    (neg_le_neg (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))).trans (neg_abs_le _)
  exact h2.trans h1

end GlobalTheory.NefOfGen

end
end
