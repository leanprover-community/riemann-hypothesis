import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.ExistsGap
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ConvMul
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OrthogonalKeepingHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RepAlg

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

section AlgExPf

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem keepQ {Q : Submodule ℂ H} {Γ : Type} {op : Γ → (H →L[ℂ] H)} {v : Γ → ℂ}
    (hQ : ∀ x, ∀ f ∈ Q, op x f ∈ Q ∧ star (op x) f ∈ Q) {y : (H →L[ℂ] H) × ℂ}
    (hy : y ∈ StarAlgebra.adjoin ℂ (Set.range fun x => (op x, v x))) :
    (∀ f ∈ Q, y.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1) f ∈ Q := by
  induction hy using StarAlgebra.adjoin_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨fun f hf => (hQ a f hf).1, fun f hf => (hQ a f hf).2⟩
  | algebraMap r =>
    have h1 : (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = r • (1 : H →L[ℂ] H) := by
      rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simpa using Q.smul_mem r hf
    · simpa [star_smul] using Q.smul_mem (star r) hf
  | add x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact Q.add_mem (hx.1 f hf) (hy.1 f hf)
    · rw [Prod.fst_add, star_add]
      exact Q.add_mem (hx.2 f hf) (hy.2 f hf)
  | mul x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact hx.1 _ (hy.1 f hf)
    · rw [Prod.fst_mul, star_mul]
      exact hy.2 _ (hx.2 f hf)
  | star x _ hx =>
    refine ⟨fun f hf => hx.2 f hf, fun f hf => ?_⟩
    have : (star (star x).1) = x.1 := by rw [Prod.fst_star, star_star]
    rw [this]
    exact hx.1 f hf

end AlgExPf

end UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.Zero.ConvolutionTheory.EB.algEx :
    UpperTheory.Zero.ConvolutionTheory.EB.AlgEx := by
  intro H _ _ _ Q _ Γ op v hc hs hQ
  let s : Set ((H →L[ℂ] H) × ℂ) := Set.range fun x => (op x, v x)
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hc x y).eq (mul_comm _ _)
  have hcs : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hs x y).eq (mul_comm _ _)
  letI : CommRing (StarAlgebra.adjoin ℂ s) := StarAlgebra.adjoinCommRingOfComm ℂ hcomm hcs
  have keep : ∀ y : StarAlgebra.adjoin ℂ s, (∀ f ∈ Q, y.1.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1.1) f ∈ Q :=
    fun y => UpperTheory.Zero.ConvolutionTheory.EB.keepQ hQ y.2
  let res : StarAlgebra.adjoin ℂ s → (Q →L[ℂ] Q) := fun y =>
    (y.1.1 ∘L Q.subtypeL).codRestrict Q fun q => (keep y).1 q q.2
  let R : StarAlgebra.adjoin ℂ s →⋆ₐ[ℂ] (Q →L[ℂ] Q) :=
    { toFun := res
      map_one' := by ext q; rfl
      map_mul' := fun a b => by ext q; rfl
      map_zero' := by ext q; rfl
      map_add' := fun a b => by ext q; rfl
      commutes' := fun r => by
        ext q
        have h1 : ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 = r • (1 : H →L[ℂ] H) := by
          show (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = _
          rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
        have h2 : algebraMap ℂ (Q →L[ℂ] Q) r = r • (1 : Q →L[ℂ] Q) :=
          Algebra.algebraMap_eq_smul_one r
        show ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 (q : H) = _
        rw [h1, h2]
        simp
      map_star' := fun y => by
        show res (star y) = star (res y)
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
        intro p q
        show inner ℂ (star y.1.1 (p : H)) (q : H) = inner ℂ (p : H) (y.1.1 (q : H))
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] }
  let ι : Γ → StarAlgebra.adjoin ℂ s := fun x => ⟨(op x, v x), StarAlgebra.subset_adjoin ℂ s ⟨x, rfl⟩⟩
  have all : ∀ y : StarAlgebra.adjoin ℂ s, y ∈ StarAlgebra.adjoin ℂ (Set.range ι) := by
    intro y
    induction y using StarAlgebra.adjoin_induction_subtype with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact StarAlgebra.subset_adjoin ℂ _ ⟨a, rfl⟩
    | algebraMap r => exact algebraMap_mem _ r
    | add x y hx hy => exact add_mem hx hy
    | mul x y hx hy => exact mul_mem hx hy
    | star x hx => exact star_mem hx
  have top : StarAlgebra.adjoin ℂ (Set.range ι) = ⊤ := eq_top_iff.2 fun y _ => all y
  exact ⟨{ B := StarAlgebra.adjoin ℂ s
           R := R
           P := (StarAlgHom.snd ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           F := (StarAlgHom.fst ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           ι := ι
           hF := fun _ => rfl
           hP := fun _ => rfl
           hR := fun _ _ => rfl
           top := top }⟩
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

private lemma wdVal_map {B C Γ : Type} [CommRing B] [StarRing B] [Algebra ℂ B] [Ring C] [StarRing C] [Algebra ℂ C]
    (f : B →⋆ₐ[ℂ] C) (gen : Γ → B) (w : List (Γ × Bool)) :
    f (wdVal gen w) = wdVal (fun x => f (gen x)) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp [map_star]

theorem peakAlg : PeakAlg := by
  intro H _ _ _ Q _ Γ op v 𝔄 arch a₀ x ρ ha hv hρ hs
  let gen : {γ // arch γ} → 𝔄.B := fun γ => 𝔄.ι γ
  let A : StarSubalgebra ℂ 𝔄.B := StarAlgebra.adjoin ℂ (Set.range gen)
  have hmem : ∀ γ : {γ // arch γ}, 𝔄.ι γ ∈ A := fun γ =>
    StarAlgebra.subset_adjoin ℂ (Set.range gen) (Set.mem_range_self γ)
  let p : A →⋆ₐ[ℂ] ℂ := 𝔄.P.comp A.subtype
  let a₁ : A := ⟨𝔄.ι a₀, hmem ⟨a₀, ha⟩⟩
  obtain ⟨g, hg, hn⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.peak 𝔄.B Q 𝔄.R A p a₁ (𝔄.ι x) ρ
    (by
      change 𝔄.P (𝔄.ι a₀) = 1
      rw [𝔄.hP, hv])
    hρ
    (fun s hb hsa => hs s hb fun γ hγ => by
      have h1 := hsa ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩
      have h2 : p ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩ = v γ := by
        change 𝔄.P (𝔄.ι γ) = v γ
        exact 𝔄.hP γ
      rw [← h2]
      exact h1)
  obtain ⟨J, hJ, c, w, L, -, hgw, -⟩ := PositivityTheory.Rg.BcB.F.adjWords _ _ gen (g : 𝔄.B) g.2
  refine ⟨J, hJ, c, w, ?_, ?_⟩
  · have hp : 𝔄.P (g : 𝔄.B) = 1 := hg
    rw [hgw, map_sum] at hp
    rw [← hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, wdVal_map, smul_eq_mul]
    congr 2
    funext γ
    exact (𝔄.hP γ).symm
  · have hF : op x * ((∑ j, c j • wdVal (fun γ : {γ // arch γ} => op γ) (w j)) * op a₀) =
        𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) := by
      rw [map_mul, map_mul, 𝔄.hF, 𝔄.hF, hgw, map_sum]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, wdVal_map]
      congr 2
      funext γ
      exact (𝔄.hF γ).symm
    rw [hF]
    have hnorm : ‖𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) ∘L Q.subtypeL‖ =
        ‖𝔄.R (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀))‖ := by
      refine ContinuousLinearMap.opNorm_ext _ _ fun q => ?_
      change ‖𝔄.F _ (q : H)‖ = ‖(𝔄.R _ q)‖
      rw [← 𝔄.hR]
      rfl
    rw [hnorm]
    exact hn

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

private theorem conv_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]
    (μ : Measure (H E a b)) (Φ : Matrix ι ι (H E a b → ℂ)) (c : ℂ) (f : ι → H E a b → ℂ) :
    PositivityTheory.Rg.BcB.E.conv μ Φ (c • f) = c • PositivityTheory.Rg.BcB.E.conv μ Φ f := by
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

set_option maxHeartbeats 1000000 in
theorem realAlg : RealAlg := by
  intro E _ _ _ B Q _ Γ _ t v 𝔄 a₀ g s hok hK hT hs hs0
  let gg : Γ → BGen B := fun x => Sum.inr (t x)
  let X : B.Hb →L[ℂ] B.Hb := (t a₀).op
  have hmem : ∀ y : 𝔄.B, 𝔄.F y ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X}) := by
    have hle : StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) ≤ (StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})).comap 𝔄.F := by
      refine StarAlgebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      show 𝔄.F (𝔄.ι x) ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})
      rw [𝔄.hF]
      exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)
    intro y
    have hy : y ∈ StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) := by
      rw [𝔄.top]
      exact StarSubalgebra.mem_top
    exact hle hy
  have hΦ : ∀ y : 𝔄.B, ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ (𝔄.F y * (t a₀).op) := fun y =>
    Rd.phiEx BlockFiniteConvolution.blkOp₀ BlockFiniteConvolution.blkWord₀ blkSum adjWords gg X (t a₀) (t a₀) (fun x => hok x) (hok a₀) rfl (hok a₀)
      ⟨𝔄.F y, hmem y⟩
  choose Φ hΦt hΦr using hΦ
  have hop : ∀ y : 𝔄.B, ∃ T : B.Hb →L[ℂ] B.Hb, IsROp B.D (Φ y) T ∧
      (∀ w : Q, T (Q.subtypeL w) = Q.subtypeL (𝔄.R (y * 𝔄.ι a₀) w)) ∧
      ∀ u, (∀ w : Q, inner ℂ (Q.subtypeL w) u = 0) → ∀ w : Q, inner ℂ (Q.subtypeL w) (T u) = 0 := by
    intro y
    have hTy : 𝔄.F y * (t a₀).op = 𝔄.F (y * 𝔄.ι a₀) := by rw [map_mul, 𝔄.hF]
    refine ⟨_, hΦr y, fun w => ?_, fun u hu w => ?_⟩
    · rw [hTy]
      exact (𝔄.hR _ w).symm
    · rw [hTy]
      have h1 : (ContinuousLinearMap.adjoint (𝔄.F (y * 𝔄.ι a₀))) (w : B.Hb) =
          Q.subtypeL (𝔄.R (star (y * 𝔄.ι a₀)) w) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
        exact (𝔄.hR _ w).symm
      have h2 := hu (𝔄.R (star (y * 𝔄.ι a₀)) w)
      rw [← h1, ContinuousLinearMap.adjoint_inner_left] at h2
      exact h2
  have hC : ({1} ∪ Set.range 𝔄.ι : Set 𝔄.B).Countable :=
    (Set.countable_singleton _).union (Set.countable_range _)
  obtain ⟨M, sk, f, hlim, hk⟩ := PositivityTheory.Rg.BcB.E2.orthogonal_keeping_holds E B.a B.b B.D B.I Q Q.subtypeL (fun w => rfl) 𝔄.B 𝔄.R s
    (𝔄.ι a₀) ({1} ∪ Set.range 𝔄.ι) Φ g hs hs0 hC (Or.inl rfl) hΦt hop
    (fun j w => (Submodule.mem_orthogonal _ _).1 (hT.1 j) w w.2) hT.2
  refine ⟨fun k x => sk k (𝔄.ι x), f, fun x => hlim _ (Or.inr ⟨x, rfl⟩), fun k => ?_⟩
  obtain ⟨h0, hc, hne, hL, hW, hconv, horth⟩ := hk k
  have hO := fun x => BlockFiniteConvolution.blkOp₀ E B (t x) (t a₀) (hok x) (hok a₀)
  have ha : PositivityTheory.Rg.BcB.E.conv B.D.μ (t a₀).Φ (f k) = sk k (𝔄.ι a₀) • f k := by
    have h1 := hconv 1 (Or.inl rfl)
    rw [one_mul] at h1
    rw [← h1]
    refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D (hO a₀).1 (hΦt 1) ?_ (hΦr 1) hc hL
    rw [map_one, one_mul]
    exact (hO a₀).2.1
  have hx : ∀ x, PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) = sk k (𝔄.ι x) • f k := by
    intro x
    have h1 := hconv (𝔄.ι x) (Or.inr ⟨x, rfl⟩)
    have hok' := (hO x).2.2.1
    have hm := BlockFiniteConvolution.blkOp₀ E B _ _ hok' hok'
    have h2 : PositivityTheory.Rg.BcB.E.conv B.D.μ ((t x).mul (t a₀)).Φ (f k) = PositivityTheory.Rg.BcB.E.conv B.D.μ (Φ (𝔄.ι x)) (f k) := by
      refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D hm.1 (hΦt _) ?_ (hΦr _) hc hL
      rw [𝔄.hF, ← (hO x).2.2.2.1]
      exact hm.2.1
    have h3 := (UpperTheory.Zero.ConvolutionTheory.EB.convMul E B (f k) hc).1 (t x) (t a₀) (hok x) (hok a₀)
    rw [ha, conv_smul', h2, h1, map_mul] at h3
    calc PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k)
        = (sk k (𝔄.ι a₀))⁻¹ • (sk k (𝔄.ι a₀)) • PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) := (inv_smul_smul₀ h0 _).symm
      _ = (sk k (𝔄.ι a₀))⁻¹ • ((sk k (𝔄.ι x) * sk k (𝔄.ι a₀)) • f k) := by rw [← h3]
      _ = sk k (𝔄.ι x) • f k := by
        rw [smul_smul]
        congr 1
        field_simp
  exact ⟨h0, ⟨hc, hne, hL, ⟨M, hW⟩, hx⟩, horth⟩

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

private theorem rep_sum {B : Block E} {χa : InfinitePlace E → Inf B.a} {χb : InfinitePlace E → Inf B.b}
    {ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)} {J : Type} [Fintype J] (c v : J → ℂ)
    (U : J → (B.Hb →L[ℂ] B.Hb)) (R : J → ℝ) (hR : ∀ j, 0 ≤ R j)
    (h : ∀ j, Rep B χa χb ψ (v j) (R j) (U j)) :
    Rep B χa χb ψ (∑ j, c j * v j) (∑ j, R j) (∑ j, c j • U j) := by
  choose C hC hv hU using h
  refine ⟨⟨Σ j, (C j).J, Finset.univ.sigma fun j => (C j).s, fun p => c p.1 * (C p.1).c p.2,
    fun p => (C p.1).t p.2⟩, ?_, ?_, ?_⟩
  · rintro ⟨j, i⟩ hi
    have hi' : i ∈ (C j).s := (Finset.mem_sigma.1 hi).2
    obtain ⟨h1, h2, h3, h4⟩ := hC j i hi'
    have hle : R j ≤ ∑ k, R k := Finset.single_le_sum (fun k _ => hR k) (Finset.mem_univ j)
    exact ⟨h1, h2, h3.trans hle, h4.trans hle⟩
  · simp only [Cmb.val]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hv j]
    simp only [Cmb.val, Finset.mul_sum, mul_assoc]
  · simp only [Cmb.op]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hU j]
    simp only [Cmb.op, Finset.smul_sum, mul_smul]

private theorem rep_word {B : Block E} {χa : InfinitePlace E → Inf B.a} {χb : InfinitePlace E → Inf B.b}
    (hA : ∀ v, IsHerm (χa v)) (hB : ∀ v, IsHerm (χb v)) {Γ : Type} (t : Γ → PT B) (t₀ : PT B) (h₀ : t₀.Ok)
    (ht : ∀ x, (t x).Ok ∧ (t x).ψ = t₀.ψ) (hm : mulF B.ν t₀.ψ t₀.ψ = t₀.ψ) (ha : adjF t₀.ψ = t₀.ψ)
    (w : List (Γ × Bool)) :
    ∃ R, 0 ≤ R ∧ Rep B χa χb t₀.ψ (wdVal (fun x => (t x).val χa χb) w * t₀.val χa χb) R
      (wdVal (fun x => (t x).op) w * t₀.op) := by
  obtain ⟨-, hp, -, hmul⟩ := repAlg E B χa χb
  induction w with
  | nil => exact ⟨max t₀.T t₀.r, le_max_of_le_left h₀.T, by simpa [wdVal] using hp t₀ h₀⟩
  | cons p w ih =>
    obtain ⟨R, hR, hrep⟩ := ih
    obtain ⟨x, b⟩ := p
    obtain ⟨hx, hψ⟩ := ht x
    obtain ⟨-, -, -, -, hadjOk, hadjOp, -, hadjVal⟩ :=
      PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t x) (t x) hx hx
    have key : ∃ R', 0 ≤ R' ∧ Rep B χa χb t₀.ψ (if b then star ((t x).val χa χb) else (t x).val χa χb) R'
        (if b then star (t x).op else (t x).op) := by
      cases b
      · refine ⟨max (t x).T (t x).r, le_max_of_le_left hx.T, ?_⟩
        have h1 := hp (t x) hx
        rw [hψ] at h1
        simpa using h1
      · refine ⟨max (t x).adj.T (t x).adj.r, le_max_of_le_left hadjOk.T, ?_⟩
        have h1 := hp _ hadjOk
        have e : (t x).adj.ψ = t₀.ψ := by
          change adjF (t x).ψ = _
          rw [hψ, ha]
        rw [hadjOp, hadjVal χa χb hA hB, e] at h1
        simpa [ContinuousLinearMap.star_eq_adjoint] using h1
    obtain ⟨R', hR', hl⟩ := key
    refine ⟨R' + R + B.c, add_nonneg (add_nonneg hR' hR) B.c_nonneg, ?_⟩
    have h2 := hmul _ _ _ _ _ _ _ _ hl hrep
    rw [hm] at h2
    have e1 : ∀ {A : Type} [Monoid A] [Star A] (g : Γ → A), wdVal g ((x, b) :: w) =
        (if b then star (g x) else g x) * wdVal g w := fun g => by simp [wdVal]
    rw [e1, e1, mul_assoc, mul_assoc]
    exact h2

theorem wordRep : WordRep := by
  intro E _ _ _ B χa χb Γ t t₀ J _ c w hA hB h₀ ht hm ha
  choose R hR hrep using fun j => rep_word hA hB t t₀ h₀ ht hm ha (w j)
  refine ⟨∑ j, R j, Finset.sum_nonneg fun j _ => hR j, ?_⟩
  have h1 := rep_sum c _ _ R hR hrep
  rw [Finset.sum_mul, Finset.sum_mul]
  simpa only [mul_assoc, smul_mul_assoc] using h1

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

theorem peakRun : PeakRun := by
  intro E _ _ _ B Q _ χa χb Γ _ t arch a₀ x g ρ hG hK hT hHa hHb ha hv hψ hmul hadj hρ hs
  have hkeep : ∀ y, ∀ f ∈ Q, (t y).op f ∈ Q ∧ star (t y).op f ∈ Q := by
    intro y f hf
    have h1 := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t y) (t y) (hG.ok y) (hG.ok y)
    obtain ⟨hT1, hR1, -, -, hadjOk, hadjOp, -, -⟩ := h1
    have h2 := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t y).adj (t y).adj hadjOk hadjOk
    refine ⟨hK _ _ hT1 hR1 f hf, ?_⟩
    rw [ContinuousLinearMap.star_eq_adjoint, ← hadjOp]
    exact hK _ _ h2.1 h2.2.1 f hf
  obtain ⟨𝔄⟩ := algEx B.Hb Q Γ (fun y => (t y).op) (fun y => (t y).val χa χb) hG.comm hG.commStar hkeep
  obtain ⟨J, hJ, c, w, hval, hnorm⟩ := peakAlg B.Hb Q Γ (fun y => (t y).op) (fun y => (t y).val χa χb) 𝔄 arch a₀ x ρ ha hv hρ
    (fun s hb hsa => hs (fun y => s (𝔄.ι y)) hsa
      (realAlg E B Q Γ t (fun y => (t y).val χa χb) 𝔄 a₀ g s hG.ok hK hT hb
        (by rw [hsa a₀ ha, hv]; exact one_ne_zero)))
  obtain ⟨R, hR, hrep⟩ := wordRep E B χa χb {γ // arch γ} (fun γ => t γ) (t a₀) J c w hHa hHb (hG.ok a₀)
    (fun γ => ⟨hG.ok γ, hψ γ γ.2⟩) hmul hadj
  refine ⟨_, R, hR, ?_, hnorm⟩
  rw [hval, hv, one_mul] at hrep
  exact hrep

end UpperTheory.Zero.ConvolutionTheory.EB
end
end
