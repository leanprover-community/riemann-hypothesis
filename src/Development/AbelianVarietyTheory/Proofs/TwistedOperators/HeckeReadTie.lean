import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitLinearModelNorm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnramifiedCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelComplexPointMatchesCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceRead
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaComparisonIffForall
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ChartCoverFOfSecBaseChange

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeckeGenConst

open ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues Formalism.IndefR.Datum

theorem eq_zero_of_rat_span {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Module ℚ V] (M : Submodule ℚ V)
    (hM : Submodule.span ℝ (M : Set V) = ⊤) {f : V → ℂ} (hf : Continuous f) (h0 : ∀ z ∈ M, f z = 0) (z : V) : f z = 0 := by
  have hcl : ∀ z, z ∈ closure (M : Set V) := by
    intro z
    have hz : z ∈ Submodule.span ℝ (M : Set V) := hM ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => exact subset_closure hx
    | zero => exact subset_closure M.zero_mem
    | add x y _ _ hx hy => exact M.toAddSubgroup.topologicalClosure.add_mem hx hy
    | smul c x _ hx =>
      have h1 : ∀ q : ℚ, (q : ℝ) • x ∈ closure (M : Set V) := fun q =>
        map_mem_closure (f := fun y : V => (q : ℝ) • y) (continuous_const_smul _) hx fun y hy => by
          beta_reduce; rw [Rat.cast_smul_eq_qsmul]; exact M.smul_mem q hy
      exact (Rat.denseRange_cast (𝕜 := ℝ)).induction_on (p := fun c : ℝ => c • x ∈ closure (M : Set V)) c
        (isClosed_closure.preimage (continuous_id.smul continuous_const)) h1
  exact (isClosed_eq hf continuous_const).closure_subset_iff.2 h0 (hcl z)

variable {D : D7}

section Period

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}

theorem perVec_add (Wt : UnfAt U k x) (v w : Fin r → D.host.E) : perVec Wt (v + w) = perVec Wt v + perVec Wt w := by
  have he : ∀ τ : D.host.E →+* ℂ, Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := fun τ => by
    funext a; simp [Data.emb]
  funext j
  simp only [perVec, Pi.add_apply]
  unfold perFr
  split_ifs <;> simp [he, Matrix.mulVec_add, hermC, map_add, mul_add, Finset.sum_add_distrib]

theorem perVec_smul (Wt : UnfAt U k x) (q : ℚ) (v : Fin r → D.host.E) : perVec Wt (q • v) = q • perVec Wt v := by
  have he : ∀ τ : D.host.E →+* ℂ, Data.emb τ (q • v) = (q : ℂ) • Data.emb τ v := fun τ => by
    funext a; simp [Data.emb, Rat.smul_def]
  funext j
  simp only [perVec, Pi.smul_apply, Rat.smul_def]
  unfold perFr
  split_ifs
  · rw [he, Matrix.mulVec_smul]; rfl
  · simp
  · simp only [he, hermC, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul, map_ratCast]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · simp
  · simp

theorem exists_theta_perVec_ne_zero {Wt : UnfAt U k x} (Y : UnitAt Wt) :
    ∃ v : Fin r → D.host.E, Y.θ (perVec Wt v) ≠ 0 := by
  by_contra hne
  push Not at hne
  let L : (Fin r → D.host.E) →ₗ[ℚ] (Fin Wt.g → ℂ) := ⟨⟨perVec Wt, perVec_add Wt⟩, perVec_smul Wt⟩
  have h0 := eq_zero_of_rat_span (LinearMap.range L) (by
    rw [eq_top_iff, ← Wt.per.2.2.2.1]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨_, perVec_lat Wt a⟩) (GlobalTheory.EtaPinnedCompare.theta_entire Y).continuous (by
    rintro _ ⟨v, rfl⟩
    exact hne v)
  have h9 := Y.c9
  simp [h0] at h9

end Period

theorem exists_const_of_orth {K : Type} [CommRing K] {n m : ℕ} {b b' g : Fin n → Fin n → K}
    (hb : ∀ a a', ∑ i, ∑ j, b' i a * g i j * b j a' = if a = a' then 1 else 0) (v : Fin m → K) :
    ∃ X : Matrix (Fin m) (Fin n) K, ∀ j a, ∑ n, X j n * b n a = v j := by
  refine ⟨fun j n => v j * ∑ a', ∑ i, b' i a' * g i n, fun j a => ?_⟩
  have h : ∑ n, (∑ a', ∑ i, b' i a' * g i n) * b n a = 1 := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun a' _ => Finset.sum_comm.trans (hb a' a)]
    simp
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [h, mul_one]

theorem exists_map_const {V : HSp D} {b : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (hb : IsONLatBasis V b) {m : ℕ}
    (v : Fin m → D.host.E) : ∃ X : Matrix (Fin m) (Fin V.rank) D.host.E, ∀ j a, ∑ n, X j n * b n a = v j :=
  exists_const_of_orth (b' := fun i a => star (b i a)) (g := V.gram) hb.1 v

theorem exists_frAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (hM : R.IsModels) (ht : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (h : GA D (Wc D i)) :
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h := by
  have e : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
    exact res_embLL T ht.alg ht.laws.pins.2.2.1
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := e ▸ T.toCore.good_σ₀
  obtain rfl : σ = res T (sg0 D A) := hσ.trans e.symm
  obtain ⟨γ, h1, h2, -⟩ := (GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn D G Pl0 T0 A T R κ v₀ hM ht i _ hg hV).2.2 h
  exact ⟨γ, h1, h2⟩

theorem cancel {ι : Type} [Fintype ι] {u ph K K' μ q w : ℂ} {e θ : ι → ℂ} (hph : ph ≠ 0) (hμ : μ ≠ 0) (hθ : ∀ a, θ a ≠ 0)
    (h1 : Complex.exp (Real.pi / 2 * ∑ a, e a) * (μ * q * w) = ph * K' * ∏ a, θ a)
    (h2 : u * (ph * K) * ∏ a, (Complex.exp (-(Real.pi / 2 * e a)) * θ a) = w) : u * (K * q) = μ⁻¹ * K' := by
  have h3 : Complex.exp (Real.pi / 2 * ∑ a, e a) * ∏ a, Complex.exp (-(Real.pi / 2 * e a)) = 1 := by
    rw [← Complex.exp_sum, ← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]
  have h4 : ∏ a, θ a ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hθ a
  rw [← h2, Finset.prod_mul_distrib] at h1
  rw [eq_inv_mul_iff_mul_eq₀ hμ]
  refine mul_left_cancel₀ (mul_ne_zero hph h4) ?_
  linear_combination h1 - μ * q * u * ph * K * (∏ a, θ a) * h3

end GlobalTheory.HeckeGenConst

open GlobalTheory.HeckeGenConst GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues in

theorem GlobalTheory.HeckeGenConst.generator_constant : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
          toC (t none : CAt σ) ^ (κ i).n *
              ((T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
                σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV)) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) (h * a)) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV hpin P p k α Rc hS h hx
    a ha C z hz hx' t ht hb
  obtain ⟨ph, b, hph, hbON, hpin⟩ := hpin
  obtain ⟨γ', hγ', hfr'⟩ := exists_frAt hMod hTie i σ hσ hV (h * a)
  obtain ⟨_, Wt', ⟨Y'⟩⟩ := exists_witness T i σ hV hTie.laws.toLawsM (hσ ▸ T.toCore.good_σ₀) (h * a)
  obtain ⟨rV, e, he, ⟨Δ, hΔ⟩, hall⟩ :=
    GlobalTheory.HeckeVacuum.omega_vacuum_hecke D G Pl0 T0 A T R hLev hFam hThP i P p k α Rc hS a ha
  obtain ⟨-, -, hom⟩ := hall Δ hΔ
  obtain ⟨v, hv⟩ := exists_theta_perVec_ne_zero Y'
  obtain ⟨X, hX⟩ := exists_map_const hbON fun j => v (Fin.cast (rank_Wc i) j)
  have hz' : ∀ a : Fin (Vc D i).rank,
      perVec Wt' v = perVec Wt' fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a := fun a => by
    congr 1
    funext m
    rw [hX]
    rfl
  have h2 := GlobalTheory.HeckeGeoRead.theta_trace_read D hHk hSL hVF G Pl0 T0 A T R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV
    P p k α Rc hS h hx a ha C z hz hx' t ht hb ph b hph hbON hpin γ' hγ' hfr' Wt' Y' e he Δ hΔ X (fun _ => perVec Wt' v) hz'
  have h1 := hpin (h * a) γ' hγ' hfr' hx' Wt' Y' X (fun _ => perVec Wt' v) hz'
  rw [thetaAt_eq, show ((1 : GA D (Vc D i)), γ' * (h * a)) = (1, γ' * h) * (1, a) by simp [mul_assoc], map_mul,
    Module.End.mul_apply, hom, map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h1
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have h3 := cancel (fun h0 => by simp [h0] at hph) (pow_ne_zero k (Units.ne_zero _)) (fun _ => hv) h1 h2
  rw [(hTie.kap i τ).2.2, hkScal, one_mul, map_pow, map_inv₀, map_natCast, inv_pow (muAt T R i P)]
  rw [rV] at h3
  exact h3
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTerm_generator_constant_via_frame : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
          toC (t none : CAt σ) ^ (κ i).n *
              ((T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
                σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV)) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) (h * a)) := by
  atlas_forward_decl GlobalTheory.HeckeGenConst.generator_constant
end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeTerm

open NumberField in
theorem splitSup {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {P : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) :
    P.asIdeal ⊔ P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  by_contra hne
  have hsub : P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ P.asIdeal :=
    le_sup_right.trans (P.isMaximal.eq_of_le hne le_sup_left).ge
  apply h
  rw [Formalism.L2.Col.conjIdeal_asIdeal]
  refine (P.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_).symm
  rw [Formalism.L2.Col.mem_conjP]
  have : Formalism.L2.Col.cO D.host.E a = H.bar a := RingOfIntegers.ext (H.bar_eq a).symm
  rw [this]
  exact hsub (Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ha)

theorem phiW_unfold {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    castDict hV (T.phiJ j σ a f) g = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
      (T.cE j σ (castDict hV (T.dict j σ) g).1 * castDict hV (T.mu j σ) g *
        rdU (T.U j σ) f (castDict hV (T.dict j σ) g).1 (castDict hV (T.dict j σ) g).2) := by
  subst hV
  rfl

theorem heckeTerm : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
          ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C, (∃ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z) ∧
          ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n,
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
              σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f z) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) := by
  intro D hP hS hVF G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeKernel_complex_point_matches_cosets D hP hS hVF G Pl0 T0 A T R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
  refine ⟨e, fun C => ⟨?_, fun z hz f hf => ?_⟩⟩
  · have hsp := splitSup T.Q.H hs.1.1
    have hHP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p :=
      GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsp, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    have hT := hP.2.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hHP
    exact @hT (CAt σ) _ (inferInstanceAs (IsAlgClosed ℂ)) _ _ C
  · obtain ⟨hx', t, ht1, hB⟩ := he C z hz
    have hg := GlobalTheory.T.heckeTerm_generator_constant_via_frame D hP hS hVF G Pl0 T0 A T R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
      _ (e C).2 C z hz hx' t ht1 hB
    have hw := GlobalTheory.FrameEval.evR_frBor _ _ _ _ _ _ (CAt σ) _ _ f hf t _ z hB
    have hwc : wchar (ex (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) (κ i).n) t = (t none : CAt σ) ^ (κ i).n := by
      unfold wchar
      rw [Finset.prod_eq_single none (fun j _ hj => by rw [ht1 j hj]; simp) (fun h0 => absurd (Finset.mem_univ _) h0)]
      rfl
    rw [hwc] at hw
    show _ = _ * castDict hV (T.phiJ ((i : ℕ) + 1) σ (wtA (κ i)) f) (h * (e C : GA D (Wc D i)))
    rw [phiW_unfold]
    have hr : rdU (T.U ((i : ℕ) + 1) σ) f (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1
        (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 =
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) := dif_pos hx'
    rw [hr, hw]
    have hz' : toC ((t none : CAt σ) ^ (κ i).n * evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) =
        toC (t none : CAt σ) ^ (κ i).n * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) := rfl
    rw [hz']
    linear_combination ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩))) * hg

end GlobalTheory.HeckeTerm
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
          ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C, (∃ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z) ∧
          ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n,
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
              σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f z) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) := by
  atlas_forward_decl GlobalTheory.HeckeTerm.heckeTerm
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeReadProof

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

theorem phiW_eq {D : D7} (T : CoreJ D) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R ((i : ℕ) + 1)) (h : GA D (Wc D i))
    (hx : (dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (dictW T i σ hV h).1).dom) :
    phiW T i σ hV a f h = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := by
  show T.phiJ _ σ a f _ = _
  rw [CoreJ.phiJ_apply]
  simp only [Core.phiAd, Pi.smul_apply, smul_eq_mul, adel, rdU, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [dictW, castDict] at hx ⊢
  split_ifs with h1
  · ring
  · exact absurd hx h1

theorem heckeReadTie (hSL : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D) (hVF : ∀ D, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D) :
    GlobalTheory.HeckeSupSt.HeckeReadTie := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthP ht i σ hσ hV hpin
  intro P p k α Rc hs cq f g hf hg hr h
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  have hgood : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  obtain ⟨hx, -, -⟩ := exists_witness T i σ hV ht.laws.toLawsM hgood h
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeReading_kernels_match_cosets_through_frame D GlobalTheory.HeckePointLaw.heckePointLaws (hSL D) (hVF D) G Pl0 T0 A T R F κ v₀ hlev hgrp hfam
    hmod hthP ht i σ hσ hV hpin P p k α Rc hs h hx
  have hfin : Finite (hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) := Finite.of_equiv _ e.symm
  rw [phiW_eq T i σ hV _ g h hx]
  have hr' := hr (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)
  have e1 : toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c g
      ((T.U ((i : ℕ) + 1) σ).un (dictW T i σ hV h).1 ⟨(dictW T i σ hV h).2, hx⟩)) =
      σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * ∑ᶠ C,
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) := by
    refine (congrArg toC hr').trans ?_
    have hs1 : σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) = σ cq * σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) := by
      simp only [hkScal, one_mul, map_mul]
    show σ (hkScal T.Q.c cq P.asIdeal k D.R.nV) * toC (hkVal _ _ _ _ f _) = _
    rw [hs1]
    congr 1
    unfold hkVal
    show (∑ᶠ C, toC (hkTerm _ _ _ _ f _ C)) = _
    refine finsum_congr fun C => ?_
    unfold hkTerm
    split_ifs with h1
    · rfl
    · exact absurd (he C).1 h1
  rw [e1]
  have e2 : ∀ C, (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      (T.cE ((i : ℕ) + 1) σ (dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
      σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f (he C).1.choose) =
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) :=
    fun C => (he C).2 _ (he C).1.choose_spec f hf
  have e3 : ∑ᶠ C, (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) =
      (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA (κ i)) f (h * a) := by
    rw [finsum_comp_equiv e (f := fun a : Rc =>
      (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * (a : GA D (Wc D i))))]
    rw [finsum_eq_sum_of_fintype, Finset.sum_coe_sort Rc
      (fun a => (muAt T R i P)⁻¹ ^ k * phiW T i σ hV (wtA (κ i)) f (h * a)), Finset.mul_sum]
  rw [mul_assoc (σ cq) ((muAt T R i P)⁻¹ ^ k), ← e3, ← finsum_congr e2, ← mul_finsum]
  ring

end GlobalTheory.HeckeReadProof
end
end
