import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.REndoOf
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HyperbolicEntryBounds.ArchFinal
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RepAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CmbEllOf
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenC
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SatCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.IdmAct
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.ThetaFixTop

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.arEx :
    UpperTheory.Zero.ConvolutionTheory.EB.ArEx := by
  intro E _ _ _ a b l₁ l₂ D
  haveI : BorelSpace (G a) := ⟨rfl⟩
  haveI : BorelSpace (G b) := ⟨rfl⟩
  haveI : BorelSpace (Hf E a b) := ⟨rfl⟩
  haveI : LocallyCompactSpace (G a) := lc_G a
  haveI : LocallyCompactSpace (G b) := lc_G b
  let μa : Measure (G a) := Measure.haar
  let μb : Measure (G b) := Measure.haar
  have ha : μa.IsHaarMeasure := inferInstance
  have hb : μb.IsHaarMeasure := inferInstance
  obtain ⟨ν, hν, hν', hcomp⟩ := compatEx E a b D μa μb
  obtain ⟨-, -, ca, hca0, hca⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E a
  obtain ⟨-, -, cb, hcb0, hcb⟩ := GlobalTheory.CompanionTheory.Growth.size_facts E b
  obtain ⟨bump, T, hT, hbump, hone⟩ := PositivityTheory.Rg.BcB.F.F0.bump_one (InfinitePlace E ⊕ InfinitePlace E)
    (Sum.elim (fun v => cas (UpperTheory.Zero.ConvolutionTheory.EB.chi l₁ v)) fun v => cas (UpperTheory.Zero.ConvolutionTheory.EB.chi l₂ v))
    (fun i => by cases i <;> exact PositivityTheory.Rg.BcB.F.F0.cas_infOf_im _)
  obtain ⟨_, hKa⟩ := PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1 a
  obtain ⟨_, hKb⟩ := PositivityTheory.RgBcC.wave_existence_speed_multiplicity.2.2.1 b
  let Ma := UpperTheory.Zero.ConvolutionTheory.EB.Ml l₁
  let Mb := UpperTheory.Zero.ConvolutionTheory.EB.Ml l₂
  exact ⟨{
    μa := μa
    μb := μb
    ν := ν
    ha := ha
    hb := hb
    hν := hν
    hν' := hν'
    compat := hcomp
    c := max ca cb
    c_nonneg := le_max_of_le_left hca0
    ca := fun g h => (hca g h).trans (by gcongr; exact le_max_left _ _)
    cb := fun g h => (hcb g h).trans (by gcongr; exact le_max_right _ _)
    bump := bump
    T := T
    T_nonneg := hT
    isBump := hbump
    ka := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose
    kb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose
    kera := fun w v => ((hKa μa (Ma v)).1 w bump T hbump).choose_spec
    kerb := fun w v => ((hKb μb (Mb v)).1 w bump T hbump).choose_spec
    one := by simpa [Fintype.prod_sum_type] using hone }⟩
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.lvEx :
    UpperTheory.Zero.ConvolutionTheory.EB.LvEx := by
  intro E _ _ _ a b Z φ h
  have key : ∀ w : Pl E, ∃ (A : Subgroup (GLw a w)) (B : Subgroup (GLw b w)),
      IsOpen (A : Set (GLw a w)) ∧ IsOpen (B : Set (GLw b w)) ∧ A ≤ KGL w a ∧ B ≤ KGL w b ∧
      (w ∉ Z → A = KGL w a ∧ B = KGL w b) ∧ (w ∈ Z → IsHecke (A.prod B) (φ w)) := by
    intro w
    by_cases hw : w ∈ Z
    · obtain ⟨K', ho, hle, hH⟩ := h w hw
      refine ⟨K'.comap (MonoidHom.inl _ _), K'.comap (MonoidHom.inr _ _), ?_, ?_, ?_, ?_,
        fun h' => absurd hw h', fun _ => ⟨hH.1, ?_⟩⟩
      · exact ho.preimage (continuous_id.prodMk continuous_const)
      · exact ho.preimage (continuous_const.prodMk continuous_id)
      · intro x hx
        exact (hle hx).1
      · intro y hy
        exact (hle hy).2
      · rintro ⟨x, y⟩ ⟨hx, hy⟩ g
        have hxy : ((x, y) : GLw a w × GLw b w) ∈ K' := by
          have := K'.mul_mem hx hy
          simpa using this
        exact hH.2 _ hxy g
    · exact ⟨KGL w a, KGL w b, (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
        (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, le_rfl, le_rfl,
        fun _ => ⟨rfl, rfl⟩, fun h' => absurd h' hw⟩
  choose A B hA hB hA' hB' hoff hfix using key
  exact ⟨⟨A, B, hA, hB, hA', hB', hoff⟩, hfix⟩
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

theorem powRep : PowRep := by
  intro E _ _ _ a b l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hφ hR hU
  obtain ⟨-, -, hpt, hval, -⟩ := ptOk E a b l₁ l₂ D A
  obtain ⟨-, -, -, -, -, hfx, -, -⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨hidm, -⟩ := hkMul E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨-, hrep, hmono, hmul⟩ := repAlg E A.blk (chi l₁) (chi l₂)
  obtain ⟨hrt₁, hrt₂, -⟩ := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.rtAlg' E A.blk u₁ u₂
  have hc : 0 ≤ A.blk.c := A.c_nonneg
  have ok₁ : (A.ptB (A.fx S L T φ (fun _ => .one) fun _ => .one)).Ok :=
    hpt _ _ _ (hfx T φ _ _ hφ).1
  have ok₂ : (A.ptB (rt u₁ u₂ (A.idm S L))).Ok := by
    obtain ⟨r, hr⟩ := hrt₂ (A.ptB (A.idm S L)) (hpt _ _ _ hidm)
    exact hpt _ _ _ hr.ψ
  refine ⟨ok₁, ok₂, ?_⟩
  set t₁ := A.ptB (A.fx S L T φ (fun _ => .one) fun _ => .one) with ht₁
  set t₂ := A.ptB (rt u₁ u₂ (A.idm S L)) with ht₂
  have r₁0 : 0 ≤ max t₁.T t₁.r := le_max_of_le_left ok₁.T
  have r₂0 : 0 ≤ max t₂.T t₂.r := le_max_of_le_left ok₂.T
  have base₁ : Rep A.blk (chi l₁) (chi l₂) t₁.ψ 1 (max t₁.T t₁.r) t₁.op := by
    have := hrep t₁ ok₁
    rwa [hval] at this
  have base₂ : Rep A.blk (chi l₁) (chi l₂) t₂.ψ 1 (max t₂.T t₂.r) t₂.op := by
    have := hrep t₂ ok₂
    rwa [hval] at this
  have step : ∀ k : ℕ, Rep A.blk (chi l₁) (chi l₂)
      (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) 1
      (max t₁.T t₁.r + k * (R + A.blk.c)) (t₁.op * U ^ k) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, mul_one]
      exact base₁
    | succ k ih =>
      have h := hmul _ _ _ _ _ _ _ _ ih hU
      rw [(hfx T φ _ _ hφ).2.2 e₁ e₂, one_mul] at h
      have e : max t₁.T t₁.r + (k : ℝ) * (R + A.blk.c) + R + A.blk.c =
          max t₁.T t₁.r + ((k + 1 : ℕ) : ℝ) * (R + A.blk.c) := by
        push_cast; ring
      rw [e, mul_assoc, ← pow_succ] at h
      exact h
  refine ⟨max t₁.T t₁.r + max t₂.T t₂.r + A.blk.c, R + A.blk.c, by positivity, by positivity, fun k => ?_⟩
  have h := hmul _ _ _ _ _ _ _ _ (step k) base₂
  rw [one_mul] at h
  have hψ : mulF A.blk.ν (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) t₂.ψ =
      rt u₁ u₂ (A.fx S L T φ (fun w => (e₁ w).pow k) fun w => (e₂ w).pow k) := by
    show mulF A.blk.ν _ (rt u₁ u₂ (A.idm S L)) = _
    rw [hrt₁, (hfx T φ _ _ hφ).2.1]
  rw [hψ] at h
  refine hmono _ _ _ _ _ (le_of_eq ?_) h
  ring

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem heckeFunction_mul (a b : ℕ) (w : Pl E) (x y : Ex (Fin (a + 1) × Fin (b + 1))) :
    fn2 a b w (x.mul y) = PositivityTheory.Rg.BcN.F2.mconv (fn2 a b w x) (fn2 a b w y) := rfl

private theorem heckeFunction_one (a b : ℕ) (w : Pl E) :
    fn2 a b w (.one : Ex (Fin (a + 1) × Fin (b + 1))) = (K2 a b w : Set _).indicator 1 := rfl

private theorem hecke_unit (a b : ℕ) (w : Pl E) :
    IsHecke (K2 a b w) (((K2 a b w : Subgroup _) : Set (GLw a w × GLw b w)).indicator (1 : GLw a w × GLw b w → ℂ)) :=
  UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w .one

private theorem mconv_unit (a b : ℕ) (w : Pl E) {f : LF a b w} (hf : IsHecke (K2 a b w) f) :
    PositivityTheory.Rg.BcN.F2.mconv f ((K2 a b w : Set _).indicator 1) = f := by
  have L : Lv a b (∅ : Finset (Pl E)) := ⟨fun w => KGL w a, fun w => KGL w b,
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
    fun w => (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, fun _ => le_rfl, fun _ => le_rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩
  exact ((locAlg E a b ∅ L w).2.2.2.2 f hf).1

private theorem heckeFunction_one_pow (a b : ℕ) (w : Pl E) (k : ℕ) :
    fn2 a b w ((.one : Ex (Fin (a + 1) × Fin (b + 1))).pow k) = (K2 a b w : Set _).indicator 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show fn2 a b w (((.one : Ex (Fin (a + 1) × Fin (b + 1))).pow k).mul .one) = _
    rw [heckeFunction_mul, ih, heckeFunction_one]
    exact mconv_unit a b w (hecke_unit a b w)

theorem seenFam : SeenFam := by
  intro E _ _ _ a b S Z L hZ φ T e₁ e₂ hφ hT
  have hposition := positionTest E a b S Z L hZ
  have hZw : ∀ w ∈ Z, seen φ L.ln w = φ w := by
    intro w hw
    funext y
    have h := ((locAlg E a b Z L w).2.2.2.1 (φ w) (hφ w hw)).1
    simp only [seen, if_pos (hZ w hw).2]
    exact congrFun h y
  refine ⟨hZw, fun k => ⟨⟨hT.1, fun w hw hs x => ?_⟩, ?_, ?_, ?_⟩⟩
  · rw [Ex.ev_pow, hT.2 w hw hs]
    simp [Ex.ev]
  · funext w
    by_cases hwZ : w ∈ Z
    · have h := hZw w hwZ
      funext y
      have h' := congrFun h y
      simp only [seen, if_pos (hZ w hwZ).2, intersection_update_fsHerm_neg_one, fam, if_pos hwZ] at h' ⊢
      exact h'
    · by_cases hwT : w ∈ T
      · by_cases hs : IsSplitAt w
        · funext y
          simp only [seen, if_pos hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_pos hwT]
          rfl
        · funext y
          simp only [seen, if_neg hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_pos hwT]
          rw [heckeFunction_mul, hT.2 w hwT hs, heckeFunction_one_pow, mconv_unit a b w (UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.exHecke2 E a b w _)]
      · by_cases hs : IsSplitAt w
        · funext y
          simp only [seen, if_pos hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_neg hwT]
          exact congrFun (mconv_unit a b w (hecke_unit a b w)) y
        · funext y
          simp only [seen, if_neg hs, intersection_update_fsHerm_neg_one, fam, if_neg hwZ, if_neg hwT]
  · have h : fam Z T φ e₁ e₂ k = intersection_update_fsHerm_neg_one Z T φ fun w => ((e₁ w).pow k).mul ((e₂ w).pow k) := by
      funext w
      simp only [fam, intersection_update_fsHerm_neg_one]
    rw [h]
    exact (hposition.2.2 φ hφ).2 T _
  · funext B₁ B₂
    simp only [UpperTheory.V.Z.Tf.GlobalTraceComparison.val, ev2, Ex.ev_pow, ← Finset.prod_pow, mul_pow]

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section
open UpperTheory.Zero.ConvolutionTheory.EB in
theorem UpperTheory.Zero.ConvolutionTheory.EB.cmbEll :
    UpperTheory.Zero.ConvolutionTheory.EB.CmbEll := cmbEll_of cmbTest seenFam positionTest lefL ffAlg
end

section
theorem UpperTheory.Zero.ConvolutionTheory.EB.powNorm :
    UpperTheory.Zero.ConvolutionTheory.EB.PowNorm := by
  intro H _ _ Q U ρ hQ hU k
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hU
  have hb : ∀ f ∈ Q, ‖U f‖ ≤ ρ * ‖f‖ := by
    intro f hf
    exact (U ∘L Q.subtypeL).le_of_opNorm_le hU ⟨f, hf⟩
  have key : ∀ k : ℕ, ∀ f ∈ Q, (U ^ k) f ∈ Q ∧ ‖(U ^ k) f‖ ≤ ρ ^ k * ‖f‖ := by
    intro k
    induction k with
    | zero =>
      intro f hf
      simp [hf]
    | succ k ih =>
      intro f hf
      obtain ⟨h1, h2⟩ := ih f hf
      have e : (U ^ (k + 1)) f = U ((U ^ k) f) := by
        rw [pow_succ']
        rfl
      rw [e]
      refine ⟨hQ _ h1, (hb _ h1).trans ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hρ
  refine ⟨fun f hf => (key k f hf).1, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hρ k) fun q => ?_
  exact (key k q q.2).2
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem lAbs_fin {u : GL (Fin n) (Af E)} (hu : u ∈ Kf E n) : logAbs (finGL E n u).val.det = 0 := by
  have hc : Continuous fun u : GL (Fin n) (Af E) => logAbs (finGL E n u).val.det :=
    (DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).comp GlobalTheory.BCT.GlobLev.continuous_finGL_ad
  obtain ⟨C, hC⟩ := (GlobalTheory.CompanionTheory.EulerV.isCompact_Kf (E := E) (n := n)).exists_bound_of_continuousOn hc.continuousOn
  refine DiscreteGroups.T1.G.CP.eq_zero_of_nat_mul_le (C := C) fun m => ?_
  have h := hC (u ^ m) (pow_mem hu m)
  rw [map_pow, Real.norm_eq_abs, DiscreteGroups.T1.G.CP.lAbs_pow, abs_mul, Nat.abs_cast] at h
  exact h

private theorem lAbs_inf (k : Kinf E n) : logAbs (infGL E n (Unitary.toUnits k)).val.det = 0 := by
  rw [← UpperTheory.V.Cm.infEmb_cptEq]
  exact DiscreteGroups.T1.G.CP.lAbs_maxCompact (UpperTheory.V.Cm.cptEq E n k).2

private theorem typeB_untwist {K : Subgroup (GL (Fin n) (Af E))} {W : Submodule ℂ (Kinf E n → ℂ)} (hK : K ≤ Kf E n)
    {φ ψ : Sm E n} {z : ℂ} (h : ∀ y, φ.1 y = ψ.1 y * Complex.exp (z * logAbs y.val.det)) (hT : TypeB K W φ) :
    TypeB K W ψ := by
  have hψ : ∀ y, ψ.1 y = Complex.exp (-(z * logAbs y.val.det)) * φ.1 y := fun y => by
    rw [h y, mul_comm (ψ.1 y), ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  refine ⟨fun u hu g => ?_, fun g => ?_⟩
  · rw [hψ, hψ g, hT.1 u hu g, DiscreteGroups.T1.G.CP.lAbs_mul, lAbs_fin (hK hu), add_zero]
  · have e : (fun k : Kinf E n => ψ.1 (g * infGL E n (Unitary.toUnits k))) =
        Complex.exp (-(z * logAbs g.val.det)) • fun k : Kinf E n => φ.1 (g * infGL E n (Unitary.toUnits k)) := by
      funext k
      rw [hψ, DiscreteGroups.T1.G.CP.lAbs_mul, lAbs_inf, add_zero]
      rfl
    rw [e]
    exact W.smul_mem _ (hT.2 g)

private theorem adjM_test {a b : ℕ} {ι : Type} {Φ : Matrix ι ι (H E a b → ℂ)} (h : IsTestM Φ) : IsTestM (adjM Φ) := by
  intro i j
  refine ⟨Complex.continuous_conj.comp ((h j i).1.comp continuous_inv), ?_⟩
  have h1 : HasCompactSupport fun y : H E a b => Φ j i y⁻¹ := (h j i).2.comp_homeomorph (Homeomorph.inv _)
  exact h1.comp_left (g := starRingEnd ℂ) (map_zero _)

private theorem keepsOrth {ι : Type} [Fintype ι] (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    (Φ : Matrix ι ι (H E n 0 → ℂ)) (T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (hΦ : IsTestM Φ) (hT : IsROp D Φ T) :
    ∀ f ∈ (piSp D π ι)ᗮ, T f ∈ (piSp D π ι)ᗮ := by
  intro f hf
  rw [Submodule.mem_orthogonal] at hf ⊢
  intro q hq
  have hadj : IsROp D (adjM Φ) (ContinuousLinearMap.adjoint T) :=
    ((PositivityTheory.Rg.BcB.E1.opEx_holds E n 0 D ι).2 Φ Φ T T hΦ hΦ hT hT).2.2
  have hq' := DiscreteGroups.T1.G.piInv E n hn D π hθ ι (adjM Φ) _ (adjM_test hΦ) hadj q hq
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hf _ hq'

private theorem vecEx {ι : Type} [Fintype ι] (hn : 1 ≤ n) (D : Dom E n 0) (π : CuspSub E n) (hθ : ThetaFix π)
    (ψ : Sm E n) (hψ : ψ ∈ π.V) (u : ℝ → ℂ) (hu : Continuous u) (hc : HasCompactSupport u) (i : ι) :
    ∃ v : Hs (ι := ι) D, v ∈ piSp D π ι ∧
      (∀ i' (M : ℕ), ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖(v i' : H E n 0 → ℂ) x‖ₑ ^ 2 ∂D.ν < ⊤) ∧
      ∀ f : ι → H E n 0 → ℂ, ∑ i', ∫ x, starRingEnd ℂ ((v i' : H E n 0 → ℂ) x) * f i' x ∂D.ν =
        ∫ x, starRingEnd ℂ (ψ.1 x.1 * u (ldet x)) * f i x ∂D.ν := by
  obtain ⟨hm, hw⟩ := DiscreteGroups.T1.G.Dcy.piVecEx_holds E n hn D π hθ ψ hψ u hu hc
  set w : Lp ℂ 2 D.ν := hm.toLp _ with hwd
  have hwe : (w : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * u (ldet x) := hm.coeFn_toLp
  set v : Hs (ι := ι) D := WithLp.toLp 2 (Pi.single i w) with hv
  have hvi : v i = w := by simp [hv]
  have hv0 : ∀ i', i' ≠ i → v i' = 0 := fun i' h => by simp [hv, h]
  have hz : ∀ i', i' ≠ i → (v i' : H E n 0 → ℂ) =ᵐ[D.ν] 0 := fun i' h => by
    rw [hv0 i' h]; exact Lp.coeFn_zero _ _ _
  refine ⟨v, ?_, fun i' M => ?_, fun f => ?_⟩
  · refine Submodule.le_topologicalClosure _ (Submodule.subset_span ?_)
    intro i'
    by_cases h : i' = i
    · subst h
      exact ⟨ψ, hψ, u, hu, hc, by rw [hvi]; exact hwe⟩
    · refine ⟨0, Submodule.zero_mem _, 0, continuous_const, HasCompactSupport.zero, ?_⟩
      filter_upwards [hz i' h] with x hx
      simp [hx]
  · by_cases h : i' = i
    · subst h
      rw [hvi]
      refine lt_of_eq_of_lt (lintegral_congr_ae ?_) (hw M)
      filter_upwards [hwe] with x hx
      rw [hx]
    · refine lt_of_eq_of_lt (lintegral_congr_ae (g := fun _ => 0) ?_) (by simp)
      filter_upwards [hz i' h] with x hx
      simp [hx]
  · rw [Finset.sum_eq_single i]
    · rw [hvi]
      refine integral_congr_ae ?_
      filter_upwards [hwe] with x hx
      rw [hx]
    · intro i' _ h
      refine (integral_congr_ae (g := fun _ => 0) ?_).trans (by simp)
      filter_upwards [hz i' h] with x hx
      simp [hx]
    · intro h
      exact absurd (Finset.mem_univ i) h

theorem testsEx : PiAdm → TestsEx := by
  intro hAdm E _ _ _ n hn l₁ l₂ D A π hθ K W hK hKf hW
  refine ⟨fun Φ T hΦ hT f hf => DiscreteGroups.T1.G.piInv E n hn D π hθ _ Φ T hΦ hT f hf,
    fun Φ T hΦ hT f hf => keepsOrth hn D π hθ Φ T hΦ hT f hf, ?_⟩
  obtain ⟨Y, hYπ, hYf, hY⟩ := hAdm E n hn π hθ K W hK hW
  obtain ⟨ψ, u, hψu, hS⟩ := DiscreteGroups.T1.G.Dcy.piSeen_holds E n hn D π hθ Y hYπ hYf
  choose v hvm hvw hvs using fun p : A.blk.I × ℕ =>
    vecEx (ι := A.blk.I) hn D π hθ (ψ p.2) (hψu p.2).1 (u p.2) (hψu p.2).2.1 (hψu p.2).2.2 p.1
  obtain ⟨e, he⟩ := exists_surjective_nat (Option (A.blk.I × ℕ))
  have key : ∀ o : Option (A.blk.I × ℕ), o.elim (0 : Hs (ι := A.blk.I) D) v ∈ piSp D π A.blk.I ∧
      ∀ i (M : ℕ), ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) *
        ‖((o.elim (0 : Hs (ι := A.blk.I) D) v) i : H E n 0 → ℂ) x‖ₑ ^ 2 ∂D.ν < ⊤ := by
    rintro (_ | p)
    · refine ⟨Submodule.zero_mem _, fun i M => ?_⟩
      refine lt_of_eq_of_lt (lintegral_congr_ae (g := fun _ => 0) ?_) (by simp)
      have h0 : (((0 : Hs (ι := A.blk.I) D) i : Lp ℂ 2 D.ν) : H E n 0 → ℂ) =ᵐ[D.ν] 0 := Lp.coeFn_zero _ _ _
      filter_upwards [h0] with x hx
      show ENNReal.ofReal _ * ‖(((0 : Hs (ι := A.blk.I) D) i : Lp ℂ 2 D.ν) : H E n 0 → ℂ) x‖ₑ ^ 2 = 0
      rw [hx]
      simp
    · exact ⟨hvm p, hvw p⟩
  refine ⟨fun j => (e j).elim 0 v, ⟨fun j => ?_, fun j i M => (key (e j)).2 i M⟩, ?_⟩
  · rw [Submodule.orthogonal_orthogonal]
    exact (key (e j)).1
  · intro f hO i m₂ φ hφ hne hT π' hπ' ψ' hψ' z hz
    obtain rfl : π' = π := hπ'
    have hT' : TypeB K W ψ' := typeB_untwist hKf hz hT
    refine hne (Subtype.ext (funext fun y => ?_))
    have h0 : ψ' = 0 := hS ψ' (hY ψ' hψ' hT') z fun k => ?_
    · rw [hz y, h0]; simp
    obtain ⟨j, hj⟩ := he (some (i, k))
    have h1 := hO j
    simp only [hj, Option.elim_some] at h1
    rw [hvs (i, k) f] at h1
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have e2 : x = (x.1, m₂) := Prod.ext rfl (Subsingleton.elim _ _)
    have e3 : f i x = φ.1 x.1 := by rw [hφ]; exact congrArg (f i) e2
    simp only [e3, hz x.1, ldet]

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.valNil :
    UpperTheory.Zero.ConvolutionTheory.EB.ValNil := by
  intro E _ _ _ n Z T S D B₁ B₂ e₁ e₂ hS hZ hT hd hB
  obtain ⟨-, hc, -, hsec⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E
  have hoff : ∀ w ∈ T, Off Z w ∧ Off Z (cPl w) := by
    intro w hw
    have h₁ : w ∉ Z := Finset.disjoint_left.mp hd hw
    have h₂ : cPl w ∉ Z := by
      intro h
      obtain ⟨hs, hsp⟩ := hZ _ h
      have hne : cPl (cPl w) ≠ cPl w := ((hc (cPl w)).2).mp hsp
      rw [(hc w).1] at hne
      exact hne ((hsec S hS w).2 (hT w hw) hs).symm
    exact ⟨⟨h₁, h₂⟩, h₂, by rwa [(hc w).1]⟩
  have hz : ∀ w, Off Z w → B₂ w = 0 := fun w hw =>
    Multiset.card_eq_zero.mp (UpperTheory.Zero.ConvolutionTheory.EB.satCard E 0 D w _ (hB w hw))
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
  refine Finset.prod_congr rfl fun w hw => ?_
  obtain ⟨h₁, h₂⟩ := hoff w hw
  rw [hz w h₁, hz _ h₂]
  rfl
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem pow_norm_le {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] (U : H →L[ℂ] H) (k : ℕ) :
    ‖U ^ k‖ ≤ (‖U‖ + 1) ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul ih (by linarith) (norm_nonneg _) (by positivity))

private theorem final_bd (κ g t : ℂ) (hκ : κ ≠ 0) (C a b u ρ : ℝ) (N k : ℕ) (hρ : 0 < ρ) (hu : 0 ≤ u) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ ρ ^ k) (hb : b ≤ (u + 1) ^ k)
    (h : ‖κ * 1 * g - t / 2‖ ≤ C * (1 + k) ^ N * a + C * b * (ρ / (u + 1)) ^ k) :
    ‖g - t / (2 * κ)‖ ≤ ‖κ‖⁻¹ * (2 * |C|) * (1 + k) ^ N * ρ ^ k := by
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  have e : κ * 1 * g - t / 2 = κ * (g - t / (2 * κ)) := by field_simp
  rw [e, norm_mul] at h
  have h1 : (1 : ℝ) ≤ (1 + k) ^ N := one_le_pow₀ (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have h2 : C * (1 + k) ^ N * a ≤ |C| * (1 + k) ^ N * ρ ^ k :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) ha ha0 (by positivity)
  have h3 : C * b * (ρ / (u + 1)) ^ k ≤ |C| * (1 + k) ^ N * ρ ^ k := by
    calc C * b * (ρ / (u + 1)) ^ k ≤ |C| * (u + 1) ^ k * (ρ / (u + 1)) ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self C) hb hb0 (abs_nonneg C)) (by positivity)
      _ = |C| * 1 * ρ ^ k := by
          rw [mul_assoc, ← mul_pow, mul_one]
          congr 2
          field_simp
      _ ≤ _ := by gcongr
  rw [mul_assoc, mul_assoc, le_inv_mul_iff₀ hκ']
  linarith

end UpperTheory.Zero.ConvolutionTheory.EB

open UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

set_option maxHeartbeats 800000 in
theorem UpperTheory.Zero.ConvolutionTheory.EB.rStable :
    UpperTheory.Zero.ConvolutionTheory.EB.RStable := by
  intro hFin hAdm hG hPi P hSp E _ _ _ hE n hn π hreg hdual
  haveI : Nontrivial (InfinitePlace E) := GlobalTheory.T.nontrivial_infinite_place_of_unramified E hE
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  haveI : BorelSpace (GA E 0) := ⟨rfl⟩
  have hθ : ThetaFix π := DiscreteGroups.T1.G.thetaFixOf E n hn π hdual
  obtain ⟨l₁, -, hl⟩ := hPi E hE n hn π hreg hdual
  refine ⟨l₁, fun l₂ S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨μ₁, hμ₁⟩ := haarEx E n
  obtain ⟨μ₂, hμ₂⟩ := haarEx E 0
  obtain ⟨D, -, hD⟩ := hG E n hn μ₁ μ₂
  obtain ⟨A⟩ := arEx E n 0 l₁ l₂ D
  obtain ⟨u₁, hu₁⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E n
  obtain ⟨u₂, hu₂⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E 0
  obtain ⟨κ, hκ, hell⟩ := cmbEll E hE n 0 l₁ l₂ D A μ₁ μ₂ hμ₁ hμ₂
  obtain ⟨c₀, hc₀, htr⟩ := hl l₂ D A S hS Z hZ B τ hB hτ u₁ u₂ hu₁
  refine ⟨c₀ / (2 * κ), div_ne_zero hc₀ (mul_ne_zero two_ne_zero hκ), fun φ hφ hrg => ?_⟩
  obtain ⟨L, hL⟩ := lvEx E n 0 Z φ hφ
  obtain ⟨c, hc, htest⟩ := cmbTest E n 0 l₁ l₂ D A S Z L hS hZ u₁ u₂ hu₁ hu₂
  obtain ⟨k1, k2, -⟩ := kgFacts E n S Z L.L₁ hS hZ (fun w => ⟨L.open₁ w, L.le₁ w⟩) (fun w hw => (L.off w hw).1)
  obtain ⟨k3, -, -⟩ := kgFacts E 0 S Z L.L₂ hS hZ (fun w => ⟨L.open₂ w, L.le₂ w⟩) (fun w hw => (L.off w hw).2)
  have hT := fun W hW => testsEx hAdm E n hn l₁ l₂ D A π hθ (Kg S L.L₁) W k1 k2 hW
  obtain ⟨kp, ko, -⟩ := hT ⊥ inferInstance
  haveI : CompleteSpace ((piSp D π A.blk.I)ᗮ : Submodule ℂ A.blk.Hb) := (Submodule.isClosed_orthogonal _).completeSpace_coe
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, a3⟩ := hSp E n 0 l₁ l₂ D A S Z L hS hZ {π} Set.subsingleton_singleton
    (fun π' h => by rw [Set.mem_singleton_iff.1 h]; exact hθ.1) (piSp D π A.blk.I)ᗮ ko (fun W hW => (hT W hW).2.2)
  refine ⟨J, hJ, D₁, B₁, fun j => ⟨(a1 j).1 π rfl, fun w hw => ((a1 j).2 w hw).1⟩, fun j => (a2 j).1,
    fun T hTS hd e₁ e₂ ρ hT' hρ hv => ?_⟩
  obtain ⟨U, R, hR, hU, hn'⟩ := a3 T e₁ e₂ ρ ⟨hTS, hT'⟩ hd hρ fun j => by
    rw [valNil E n Z T S (D₂ j) (B₁ j) (B₂ j) e₁ e₂ hS hZ hTS hd fun w hw => ((a1 j).2 w hw).2]
    exact hv j
  obtain ⟨o₁, o₂, r₀, r₁, hr₀, hr₁, hk⟩ := powRep E n 0 l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hL hR hU
  have b₁ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₁ o₁
  have b₂ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₂ o₂
  have hfin := hFin E n hn D π hθ A.μa A.μb A.ha A.hb _ _ Unit _ _ _ _ _ _ ((Kg S L.L₁).prod (Kg S L.L₂)) o₁.ka o₁.kb o₁.ψ
    (k1.prod k3) (fun x y u hu h => (idmAct E n 0 l₁ l₂ D A S Z L hS hZ).2.1 T φ _ _ hL x y u.1 hu.1 u.2 hu.2 h)
  obtain ⟨C, N, hb⟩ := hD π hθ A.blk.I _ _ _ _ A.tw (c * (1 + r₀)) (c * r₁) (ρ / (‖U‖ + 1)) b₁.1 b₂.1 hfin b₁.2.1 b₂.2.1
    (by positivity) (by positivity) (by positivity)
  obtain ⟨CU, u1, -, u3⟩ := hU
  obtain ⟨v1, v2⟩ := (repAlg E A.blk (chi l₁) (chi l₂)).1 CU _ _ u1
  rw [u3] at v2
  have p1 := powNorm A.blk.Hb (piSp D π A.blk.I) U _ (kp _ _ v1 v2) le_rfl
  have p2 := powNorm A.blk.Hb (piSp D π A.blk.I)ᗮ U ρ (ko _ _ v1 v2) hn'.le
  obtain ⟨-, hs⟩ := seenFam E n 0 S Z L hZ φ T e₁ e₂ hL ⟨hTS, hT'⟩
  refine ⟨‖κ‖⁻¹ * (2 * |C|), N, fun k => ?_⟩
  obtain ⟨Cm, c1, c2, c3⟩ := hk k
  have hrk : 0 ≤ r₀ + k * r₁ := by positivity
  obtain ⟨q1, q2⟩ := (repAlg E A.blk (chi l₁) (chi l₂)).1 Cm _ _ c1
  have ht := (htest φ T _ _ Cm _ hL hrg hrk c1).2
  have he := hell S Z L hS hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k Cm _ hL hrg ⟨hTS, hT'⟩ hrk c1
  have hw := htr L φ T _ _ Cm _ hL (hs k).1 hd c1
  rw [c3] at q2
  have hb' := hb k (U ^ k) Cm.Φ _ q1 q2 (p1 k).1 (p2 k).1
    (by rw [show c * (1 + r₀) + k * (c * r₁) = c * (1 + (r₀ + k * r₁)) by ring]; exact ht) hw
  rw [he, c2, (hs k).2.2.2] at hb'
  have hf := final_bd κ _ _ hκ C _ _ ‖U‖ ρ N k hρ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (p2 k).2 (pow_norm_le U k) hb'
  refine le_of_eq_of_le (congrArg norm ?_) hf
  ring
end
end
