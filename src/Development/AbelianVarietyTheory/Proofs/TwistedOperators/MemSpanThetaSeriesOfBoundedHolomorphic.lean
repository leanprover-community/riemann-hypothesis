import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVector
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunction
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDual
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilRepRationalPointsThetaFunctionsFockStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMoves
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsProperProjection
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsOrthonormalisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateModelUnitFramesEqMovedOrthonormalFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.LevMove.Rat

section Core

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_of_loc (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hx : x ∈ latHat F E (L : Set (Fin n → E)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal →
      ∀ α : FiniteAdeleRing (𝓞 F) F, evalV F v α = 1 → (∀ w, w ≠ v → evalV F w α = 0) →
        (α ⊗ₜ[F] (1 : E)) • x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))) :
    x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set N := Ideal.absNorm 𝔪 with hNdef
  have hN0 : N ≠ 0 := fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNE : ((N : 𝓞 E)) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  set c₁ : 𝓞 F := (N : 𝓞 F) with hc₁
  have hc₁0 : c₁ ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hc₁m : algebraMap (𝓞 F) (𝓞 E) c₁ ∈ 𝔪 := by rw [hc₁, map_natCast]; exact hNE
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {c₁}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set P := hfin.toFinset with hP
  have hmemP : ∀ v, v ∈ P ↔ c₁ ∈ v.asIdeal := fun v => by
    rw [hP, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  choose ind hind1 hind0 using (exists_ind (F := F))
  set e₁ : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ P, ind v with he₁
  have hev : ∀ w, evalV F w e₁ = if w ∈ P then 1 else 0 := fun w => by
    rw [he₁, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w (fun b _ hb => hind0 b w (Ne.symm hb)) (fun h => absurd hw h), hind1]
    · exact Finset.sum_eq_zero fun b hb => hind0 b w (fun h => hw (h ▸ hb))
  have hsplit : x = ((1 - e₁) ⊗ₜ[F] (1 : E)) • x + ∑ v ∈ P, (ind v ⊗ₜ[F] (1 : E)) • x := by
    rw [← Finset.sum_smul, ← TensorProduct.sum_tmul, ← he₁, ← add_smul, ← TensorProduct.add_tmul, sub_add_cancel,
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (sum_mem fun v hv => ?_)
  · refine vanish_smul_mem L 𝔪 hc₁0 hc₁m (fun w => ?_) (fun w hw => ?_) hx
    · rw [map_sub, map_one, hev]; split_ifs
      · rw [sub_self]; exact zero_mem _
      · rw [sub_zero]; exact one_mem _
    · rw [map_sub, map_one, hev, if_pos ((hmemP w).2 hw), sub_self]
  · by_cases hI : 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal
    · exact hloc v hI (ind v) (hind1 v) (hind0 v)
    · obtain ⟨c, hc, hcv⟩ := SetLike.not_le_iff_exists.1 hI
      have hc0 : c ≠ 0 := fun h => hcv (h ▸ zero_mem _)
      refine vanish_smul_mem L 𝔪 hc0 hc (ind_int (hind1 v) (hind0 v)) (fun w hw => hind0 v w ?_) hx
      rintro rfl; exact hcv hw

end Core

variable {D : D7}

theorem mov_comp {k : ℕ} {m m₂ : Matrix (Fin k) (Fin k) (AfE D)} {L L' L'' : Lt D.host.E k}
    (h : IsMov m L L') (h₂ : IsMov m₂ L' L'') : IsMov (m₂ * m) L L'' := by
  intro u
  rw [h₂ u]
  constructor
  · rintro ⟨u₁, hu₁, rfl⟩
    obtain ⟨u₀, hu₀, rfl⟩ := (h u₁).1 hu₁
    exact ⟨u₀, hu₀, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u₀, hu₀, rfl⟩
    exact ⟨m *ᵥ u₀, (h _).2 ⟨u₀, hu₀, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩

theorem smul_sandwich {R : Type} [CommRing R] {k : ℕ} (P : R) (A A' G B : Matrix (Fin k) (Fin k) R)
    (hA : P • A = P • 1) (hB : P • B = P • 1) (e : A * A' = 1) : P • (A' * G * B) = P • G := by
  have h' : P • A' = P • 1 := by
    calc P • A' = (P • 1) * A' := by rw [Matrix.smul_mul, one_mul]
      _ = (P • A) * A' := by rw [hA]
      _ = P • 1 := by rw [Matrix.smul_mul, e]
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, h', Matrix.smul_mul, one_mul, Matrix.smul_mul, ← Matrix.mul_smul, hB,
    Matrix.mul_smul, mul_one]

theorem map_mulVec_toAf {k : ℕ} (M : Matrix (Fin k) (Fin k) D.host.E) (u : Fin k → D.host.E) :
    (M.map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) *ᵥ toAf u = toAf (M *ᵥ u) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, toAf, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    TensorProduct.tmul_sum]

theorem toAf_smul {k : ℕ} (c : 𝓞 D.host.E) (u : Fin k → D.host.E) :
    toAf (c • u) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) : AfE D) • toAf u := by
  funext i
  simp only [toAf, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rfl

theorem smul_step {R : Type} [CommRing R] {k : ℕ} (P : R) (K G : Matrix (Fin k) (Fin k) R) (u w : Fin k → R)
    (h : P • K = P • G) : P • (K *ᵥ u - w) = P • (G *ᵥ u - w) := by
  rw [smul_sub, smul_sub, ← Matrix.smul_mulVec, h, Matrix.smul_mulVec]

theorem toAf_sub {k : ℕ} (u w : Fin k → D.host.E) : (toAf (u - w) : Fin k → AfE D) = toAf u - toAf w := by
  funext i
  simp only [toAf, Pi.sub_apply, TensorProduct.tmul_sub]

theorem toAf_mem {k : ℕ} {L : Lt D.host.E k} {u : Fin k → D.host.E} (hu : u ∈ L) : toAf u ∈ hatV L :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, u, hu, rfl⟩

end GlobalTheory.Ker.LevMove.Rat

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Ker.LevMove.levK_of_rat_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (γ : GL (Fin T.rank) D.host.E) (κ : Lv.J), Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) κ → ∀ (a f g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), a ∈ GinfC T → f ∈ GfC T → IsRatOf T γ (a * f) → g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤ → (mapL γ L).FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ (mapL γ L) → C.LevK Lv (g₂⁻¹ * f * g₁) κ := by
  intro D S T C Lv γ κ hred a f g₁ g₂ L ha hf hrat h1 h2 t1 t2 hLfg hLs hMfg m1 m2
  set G : Matrix (Fin T.rank) (Fin T.rank) (AfE D) :=
    (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x with hGdef
  have hfa : fmt T a = 1 := (((GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T).2.2.2.1 a ha).1
  have hff : fmt T f = G := by
    have e : fmt T (a * f) = G := by
      rw [fmt, hrat, Matrix.map_map]; rfl
    rw [← e, GlobalTheory.Ker.LevMove.fmt_mul', hfa, one_mul]
  have hfull : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have e1 : fmt T g₁ * fmt T g₁⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  have e2 : fmt T g₂ * fmt T g₂⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  obtain ⟨hto, -, -, lawsΛ⟩ := GlobalTheory.Ker.isMov_laws D T.rank C.X.Λ hfull
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Ker.isMov_laws D T.rank L ⟨hLfg, hLs⟩
  obtain ⟨-, hinv2, -, -, -⟩ := (lawsΛ _ _ e2).2 (mapL γ L) hMfg m2
  have hk : IsMov (fmt T (g₂⁻¹ * f * g₁)) C.X.Λ C.X.Λ := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul', GlobalTheory.Ker.LevMove.fmt_mul', hff]
    exact GlobalTheory.Ker.LevMove.Rat.mov_comp m1 (GlobalTheory.Ker.LevMove.Rat.mov_comp (hG γ) hinv2)
  obtain ⟨κ', hκ', hcong⟩ := hred
  refine ⟨mul_mem (mul_mem (inv_mem h2) hf) h1, hk, κ', hκ', fun i => ?_⟩
  have hb : toAf (Lv.β i) ∈ hatV C.X.Λ := GlobalTheory.Ker.LevMove.Rat.toAf_mem (Lv.β_mem i)
  have hw : toAf (∑ j, κ' j i • Lv.β j) ∈ hatV C.X.Λ :=
    GlobalTheory.Ker.LevMove.Rat.toAf_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (Lv.β_mem j))
  refine GlobalTheory.Ker.LevMove.Rat.mem_of_loc (F := D.host.F) C.X.Λ Lv.𝔪 Lv.ne_bot
    (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hw) ?_
  intro v hv α a1 a0
  have P1 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t1 hv a1 a0
  have P2 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t2 hv a1 a0
  set P : AfE D := α ⊗ₜ[D.host.F] (1 : D.host.E) with hPdef
  have hPint : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := GlobalTheory.Ker.LevMove.ind_int a1 a0
  have q1 : P • fmt T g₁ = P • 1 := by rw [smul_sub] at P1; exact sub_eq_zero.1 P1
  have q2 : P • fmt T g₂ = P • 1 := by rw [smul_sub] at P2; exact sub_eq_zero.1 P2
  have qk : P • fmt T (g₂⁻¹ * f * g₁) = P • G := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul', GlobalTheory.Ker.LevMove.fmt_mul', hff]
    exact GlobalTheory.Ker.LevMove.Rat.smul_sandwich P _ _ _ _ q2 q1 e2
  obtain ⟨d, hd⟩ : ∃ d : Fin T.rank → D.host.E, d = (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i -
    ∑ j, κ' j i • Lv.β j := ⟨_, rfl⟩
  have hx : P • (fmt T (g₂⁻¹ * f * g₁) *ᵥ toAf (Lv.β i) - toAf (∑ j, κ' j i • Lv.β j)) = P • toAf d := by
    rw [GlobalTheory.Ker.LevMove.Rat.smul_step P _ _ _ _ qk, GlobalTheory.Ker.LevMove.Rat.map_mulVec_toAf,
      ← GlobalTheory.Ker.LevMove.Rat.toAf_sub, hd]
  have hPd : P • toAf d ∈ hatV C.X.Λ := by
    rw [← hx]
    exact GlobalTheory.Ker.LevMove.int_smul_mem C.X.Λ hPint (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hw)
  change P • _ ∈ hatV (Lv.𝔪 • C.X.Λ)
  rw [hx]
  obtain ⟨s, hs, hsd⟩ := hcong i
  rw [← hd] at hsd
  obtain ⟨u, hu, m, hm, hum⟩ := Ideal.isCoprime_iff_exists.1 hs
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hsplit : P • toAf d = P • toAf ((t * s) • d) +
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((m : 𝓞 D.host.E) : D.host.E) : AfE D) • (P • toAf d) := by
    have hum' : ((t * s : 𝓞 D.host.E) : D.host.E) + ((m : 𝓞 D.host.E) : D.host.E) = 1 := by
      have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hum
      simpa using this
    rw [GlobalTheory.Ker.LevMove.Rat.toAf_smul, smul_comm P, ← add_smul, ← TensorProduct.tmul_add, hum',
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (GlobalTheory.Ker.LevMove.ideal_smul_mem C.X.Λ Lv.𝔪 hm hPd)
  refine GlobalTheory.Ker.LevMove.int_smul_mem _ hPint (GlobalTheory.Ker.LevMove.Rat.toAf_mem ?_)
  rw [mul_smul]
  exact Submodule.smul_mem _ t hsd
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLevelPoint_finitePart_mem_levelGroup : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (γ : GL (Fin T.rank) D.host.E) (κ : Lv.J), Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) κ → ∀ (a f g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), a ∈ GinfC T → f ∈ GfC T → IsRatOf T γ (a * f) → g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤ → (mapL γ L).FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ (mapL γ L) → C.LevK Lv (g₂⁻¹ * f * g₁) κ := by
  atlas_forward_decl GlobalTheory.Ker.LevMove.levK_of_rat_moves
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameDecomp

theorem hermC_mulVec {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (x *ᵥ a) (x *ᵥ b) = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
  unfold hermC
  calc ∑ p, ∑ q, (x *ᵥ a) p * τ (G p q) * conj ((x *ᵥ b) q)
      = ∑ p, ∑ q, ∑ i, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        rw [Finset.sum_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ p, ∑ i, ∑ q, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ p, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ p, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [FD.gram, Matrix.of_apply, FD.col, hermC, Finset.mul_sum, Finset.sum_mul]

theorem isometry_of_gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x y : Matrix (Fin r) (Fin r) ℂ) (hy : y.det ≠ 0) (h : FD.gram τ G x = FD.gram τ G y) (v w : Fin r → ℂ) :
    hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w) = hermC τ G v w := by
  have hyu : IsUnit y.det := isUnit_iff_ne_zero.mpr hy
  have hback : ∀ c : Fin r → ℂ, y *ᵥ (y⁻¹ *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hyu, Matrix.one_mulVec]
  calc hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w)
      = hermC τ G (x *ᵥ (y⁻¹ *ᵥ v)) (x *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = hermC τ G (y *ᵥ (y⁻¹ *ᵥ v)) (y *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [hermC_mulVec, hermC_mulVec, h]
    _ = hermC τ G v w := by rw [hback, hback]

theorem exists_real_point {D : D7} {S T : HSp D} (C : Ctx S T)
    (u : C.X.Ψ → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hu : ∀ (σ : C.X.Ψ) v w, hermC σ.1 C.X.Gm (u σ *ᵥ v) (u σ *ᵥ w) = hermC σ.1 C.X.Gm v w) :
    ∃ a ∈ GinfC T, (fun σ => (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj) = u := by
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  obtain ⟨k, hk, hkτ⟩ := GlobalTheory.FockCompare.LiftUnitary.lift_unitary D C.θ σ₀ hσ₀ T
    (fun τ => (u (C.m.e τ)).map conj) (fun τ => by
      have hcc : ((u (C.m.e τ)).map conj).map conj = u (C.m.e τ) := by
        ext i j
        simp
      simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
      rw [GlobalTheory.StabProper.unitary_iff_form, hcc]
      intro v w
      have hform := hu (C.m.e τ) v w
      rw [GlobalTheory.StabProper.hermC_eq, GlobalTheory.StabProper.hermC_eq, Equiv.symm_apply_apply] at hform
      exact hform)
  refine ⟨k, hk, ?_⟩
  funext σ
  have hcomp : compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T k) = (u σ).map conj := by
    rw [GlobalTheory.StabProper.compAt_eq, ← GlobalTheory.FockCompare.RealAction.infMat_eq, hkτ, Equiv.apply_symm_apply]
  rw [hcomp]
  ext i j
  simp

theorem frame_decomp : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  intro D S T C B hB x hx
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  obtain ⟨hon, hbB, hxeq, -, -⟩ := hob x hx
  have hz : IsONFr C.X (C.xB B) := GlobalTheory.Ker.ONBasis.isONFr_xB C hB
  have hzdom : C.xB B ∈ C.X.dom := GlobalTheory.Ker.ONBasis.mem_dom C.X hz
  have hdet : ∀ σ, (FD.mat (C.xB B) σ).det ≠ 0 := fun σ => (hzdom σ).1
  obtain ⟨a, ha, hau⟩ := exists_real_point C
    (fun σ => FD.mat (o x) σ * (FD.mat (C.xB B) σ)⁻¹)
    (fun σ v w => isometry_of_gram_eq σ.1 C.X.Gm (FD.mat (o x) σ) (FD.mat (C.xB B) σ) (hdet σ)
      (by rw [hon σ, hz σ]) v w)
  refine ⟨a, ha, b x, hbB, ?_⟩
  have hmove : C.xB (C.mvB a B) = o x := by
    funext σ
    have hσ := congrFun hau σ
    have hstep : FD.mat (C.xB (C.mvB a B)) σ
        = (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj * FD.mat (C.xB B) σ := by
      ext i j
      simp [GlobalTheory.Ker.Ctx.xB, GlobalTheory.Ker.Ctx.mvB, FD.mat, Matrix.mul_apply, map_sum]
    rw [hσ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet σ)),
      Matrix.mul_one] at hstep
    exact hstep
  rw [hmove]
  exact hxeq

end GlobalTheory.FrameDecomp
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domain_frame_eq_real_translate_mul_borel : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  atlas_forward_decl GlobalTheory.FrameDecomp.frame_decomp
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.AutRead

theorem lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ (rmul y b) = rmul (lact γ y) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map ⇑(τ : E →+* ℂ) * (mat y τ * mat b τ) =
    (γ : Matrix (Fin r) (Fin r) E).map ⇑(τ : E →+* ℂ) * mat y τ * mat b τ
  rw [Matrix.mul_assoc]

theorem ip_smul_self {n g : ℕ} (t : ℂ) {v : TF n g} (hv : SW.IsSB v) :
    SW.ip (t • v) (t • v) = (t * conj t) * SW.ip v v := by
  have hc : SW.IsSB (fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v v hv hv).2.2.2.1
  have hP : SW.IsSB (v * fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v _ hv hc).2.2.1
  have e : (fun x : Matrix (Fin n) (Fin g) ℚ => (t • v) x * conj ((t • v) x)) = (t * conj t) • (v * fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  rw [SW.ip, SW.ip, e, (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) _ _ hP hP).2.2.2.2.2.1]
  rfl

end GlobalTheory.Ker.AutRead

namespace GlobalTheory.Ker.AutRead

theorem std_mem_Vset {D : D7} {S T : HSp D} (C : Ctx S T) (M : ℕ) (hM : 0 < M) :
    stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := by
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [Red.fmtC_one]; exact Red.isMov_one _
  exact (GlobalTheory.T.self_dual_lattices_at_level D S T C).1 M 1 _ hM (Red.trivAt_one _ _) (Red.stdL_fg _) hs1

theorem wG_phi_std {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ)
    (hM : 0 < M) (hM𝔪 : (M : 𝓞 D.host.E) ∈ Lv.𝔪) (v₀ : Lt D.host.E T.rank → TF S.rank C.g)
    (hv : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L))
    (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ)
    (hμ : ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L))
    (γ : GL (Fin T.rank) D.host.E) (hγ : γ ∈ Lv.grp) (L : Lt D.host.E T.rank) (hL : L ∈ Lv.lats) :
    wG C.X C.bas C.idx γ (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) =
      μ γ L • Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank) := by
  obtain ⟨-, -, hgrp, hlat, -, -, -⟩ := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  obtain ⟨hun, k, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hL' : mapL γ L ∈ Lv.lats := ((hlat L hL).2.2.2 γ hγ).1
  have e1 := hμ γ hγ L hL ⟨k, hkJ⟩ hred
  obtain ⟨-, -, hw3, -⟩ := GlobalTheory.T.weil_action_preserves_theta_and_inner_product D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even γ hun (v₀ L) (hv L hL).1
  have hip := (hw3 (v₀ L) (hv L hL).1).1
  rw [e1, ip_smul_self _ (hv _ hL').1, (hv _ hL').2.1, (hv L hL).2.1, mul_one, Complex.mul_conj] at hip
  have hn1 : ‖μ γ L * ((Lv.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)‖ = 1 := by
    have h2 : Complex.normSq (μ γ L * ((Lv.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) = 1 := by exact_mod_cast hip
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  rw [(GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    (std_mem_Vset C M hM)).2.2.2 γ hγ ⟨k, hkJ⟩ hred _ hn1 e1, mul_inv_cancel_right₀ (Units.ne_zero _)]

theorem th_phi_ne {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ)
    (hM : 0 < M) (hM𝔪 : (M : 𝓞 D.host.E) ∈ Lv.𝔪) (v₀ : Lt D.host.E T.rank → TF S.rank C.g)
    (hv : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L))
    (B : C.Bas) (hB : C.IsB B) (L : Lt D.host.E T.rank) (hL : L ∈ Lv.lats) :
    C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) ≠ 0 := by
  intro h0
  have hstd := std_mem_Vset C M hM
  have hx := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hsb := (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    hstd).1
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ hsb
  have hsb0 := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin S.rank) (Fin C.g) _ _ hsb hsb).2.1 0
  have e : C.Th (C.xB B) ((0 : ℂ) • Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) =
      C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) := by
    rw [h2, zero_smul, h0]
  have hΦ0 : Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank) = 0 := by
    rw [(h1 _ hsb0).2 e.symm, zero_smul]
  have hip := (GlobalTheory.T.thetaTestFunction_norm_and_overlap_bound D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    hstd).1
  rw [hΦ0, SW.ip] at hip
  have ez : (fun x : Matrix (Fin S.rank) (Fin C.g) ℚ => (0 : TF S.rank C.g) x * conj ((0 : TF S.rank C.g) x)) =
      (0 : ℂ) • (0 : TF S.rank C.g) := by
    funext x; simp
  rw [ez, (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin S.rank) (Fin C.g) _ _ SW.isSB_zero SW.isSB_zero).2.2.2.2.2.1, zero_mul] at hip
  haveI : Finite (𝓞 D.host.E ⧸ Lv.𝔪) := Ideal.finiteQuotientOfFreeOfNeBot _ Lv.ne_bot
  have hpos : 0 < Nat.card Lv.J := Nat.card_pos
  exact (Nat.cast_ne_zero.2 hpos.ne') hip.symm

end GlobalTheory.Ker.AutRead

namespace GlobalTheory.Ker.AutRead

theorem read_off_automorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, F (mapL γ L) (lact γ x) = (μ γ L)⁻¹ * F L x := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hφQ hK v₀ μ hv hμ ep cf hep gL hgL F hFhol hFb hFφ
    γ hγ L hL
  obtain ⟨hΛl, -, hgrp, hlat, -, -, -⟩ := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  obtain ⟨hun, k0, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hL' : mapL γ L ∈ Lv.lats := ((hlat L hL).2.2.2 γ hγ).1
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hmv := (hJ B hB).2.2.2.2.2
  obtain ⟨e, he⟩ := (GlobalTheory.T.rational_unitary_group_structure D S T C).1
  have hγA : IsRatOf T γ (e ⟨γ, hun⟩).1 := he ⟨γ, hun⟩
  have hγAQ : (e ⟨γ, hun⟩).1 ∈ GQ T := (e ⟨γ, hun⟩).2
  have hgrpT := (GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T
  have hcomm := hgrpT.2.2.2.1
  obtain ⟨a₀, ha₀, f, hf, hγAe⟩ := hgrpT.2.2.1 (e ⟨γ, hun⟩).1
  set γA := (e ⟨γ, hun⟩).1 with hγAdef
  obtain ⟨g1f, g1t, g1m⟩ := hgL L hL
  obtain ⟨g2f, g2t, g2m⟩ := hgL (mapL γ L) hL'
  have hk := GlobalTheory.T.rationalLevelPoint_finitePart_mem_levelGroup D S T C Lv γ ⟨k0, hkJ⟩ hred a₀ f (gL L) (gL (mapL γ L)) L ha₀ hf (hγAe ▸ hγA) g1f g2f g1t g2t
    hL.1.1 (hlat L hL).2.1 hL'.1.1 g1m g2m
  set k := (gL (mapL γ L))⁻¹ * f * gL L with hkdef

  have hstd := std_mem_Vset C M hM
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [Red.fmtC_one]; exact Red.isMov_one _
  obtain ⟨hbase0, hu⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv
  obtain ⟨t, ht0, hft⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase _ (hv _ hΛl)
  have hk0 : om (1, k) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
      C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    have h1 := (hK k ⟨k0, hkJ⟩ hk).1
    rw [hft, hu t, map_smul] at h1
    exact smul_right_injective _ ht0 h1

  have hsb : ∀ L₁ ∈ Lv.lats, SW.IsSB (Lv.phi C.bas hn v₀ L₁ (stdL D.host.E S.rank)) := fun L₁ hL₁ =>
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L₁ hL₁ _ hstd).1
  have hep1 : ∀ L₁ ∈ Lv.lats, ‖ep 1‖ = 1 ∧ ‖cf (gL L₁)‖ = 1 ∧ om (1, gL L₁)
      (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
      (ep 1 * cf (gL L₁)) • C.Th (C.xB B) (Lv.phi C.bas hn v₀ L₁ (stdL D.host.E S.rank)) := by
    intro L₁ hL₁
    obtain ⟨h1, h2, h3⟩ := hgL L₁ hL₁
    have := hep 1 _ (gL L₁) L₁ (one_mem _) (Red.trivAt_one _ _) (Red.stdL_fg _) hs1 h1 h2 hL₁.1.1 h3
    simpa only [Prod.mk_one_one] using this
  have key : ∀ a ∈ GinfC T, F (mapL γ L) (lact γ (C.xB (C.mvB a B))) = (μ γ L)⁻¹ * F L (C.xB (C.mvB a B)) := by
    intro a ha
    have hBa : C.IsB (C.mvB a B) := (hmv a).1
    have ha₀a : a₀ * a ∈ GinfC T := mul_mem ha₀ ha
    have hY : lact γ (C.xB (C.mvB a B)) = C.xB (C.mvB (a₀ * a) B) := by
      rw [← ((hJ _ hBa).2.2.2.2.2 γA).2.2.2.2.2 γ hγA, ← (hmv a).2.1 γA, hγAe, mul_assoc,
        ← (hcomm a ha).2.2 f hf, ← mul_assoc, (hmv f).2.1 (a₀ * a), (hmv f).2.2.1 hf]

    have hel : γA * (gL L * a) = gL (mapL γ L) * (a₀ * a) * k := by
      have c1 : a₀ * a * (gL (mapL γ L))⁻¹ = (gL (mapL γ L))⁻¹ * (a₀ * a) := (hcomm _ ha₀a).2.2 _ (inv_mem g2f)
      have c2 : a * f = f * a := (hcomm a ha).2.2 f hf
      have c3 : a * gL L = gL L * a := (hcomm a ha).2.2 _ g1f
      rw [hkdef, hγAe]
      calc a₀ * f * (gL L * a) = a₀ * (f * a) * gL L := by rw [← c3]; group
        _ = gL (mapL γ L) * (a₀ * a * (gL (mapL γ L))⁻¹) * f * gL L := by rw [c1, ← c2]; group
        _ = _ := by group
    have s1 : φ (gL L * a) = φ (gL (mapL γ L) * (a₀ * a)) := by
      rw [← hφQ γA hγAQ, hel, (hK k ⟨k0, hkJ⟩ hk).2]
    rw [hFφ L hL a ha, hFφ (mapL γ L) hL' _ ha₀a] at s1

    have hne : C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) ≠ 0 :=
      th_phi_ne C Lv hn M hM hM𝔪 v₀ hv _ (hmv _).1 _ hL'
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ hBa).2.1
    have hX1 : om (1, γA * a * gL L) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
        (ep 1 * cf (gL L) * z a * μ γ L) •
          C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
      have p : ((1, γA * a * gL L) : GA D S × GA D T) = (1, γA) * ((1, a) * (1, gL L)) := by
        simp only [Prod.mk_mul_mk, one_mul, mul_assoc]
      rw [p, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hep1 L hL).2.2, map_smul,
        hz a ha _ (hsb L hL), map_smul, map_smul, ((GlobalTheory.T.weilRep_rationalPoints_thetaFunctions_fock D S T C om hW).2 γ γA hγA _ (hsb L hL)).1 _ hx,
        wG_phi_std C Lv hn M hM hM𝔪 v₀ hv μ hμ γ hγ L hL, hY,
        (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ ((hJ _ (hmv _).1).2.1) _ (hsb _ hL')).2.1, smul_smul, smul_smul]
    have hX2 : om (1, γA * a * gL L) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
        (ep 1 * cf (gL (mapL γ L)) * z (a₀ * a)) •
          C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
      have c3 : a * gL L = gL L * a := (hcomm a ha).2.2 _ g1f
      have p : ((1, γA * a * gL L) : GA D S × GA D T) = (1, a₀ * a) * ((1, gL (mapL γ L)) * (1, k)) := by
        have eq : γA * a * gL L = a₀ * a * (gL (mapL γ L) * k) := by
          rw [mul_assoc γA, c3, hel, ← mul_assoc (a₀ * a), ← (hcomm _ ha₀a).2.2 _ g2f]
        rw [eq]
        simp only [Prod.mk_mul_mk, one_mul]
      rw [p, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk0, (hep1 _ hL').2.2, map_smul,
        hz _ ha₀a _ (hsb _ hL'), smul_smul]
    have hsc : ep 1 * cf (gL L) * z a * μ γ L = ep 1 * cf (gL (mapL γ L)) * z (a₀ * a) :=
      smul_left_injective ℂ hne (hX1.symm.trans hX2)

    have hza : z a ≠ 0 := by
      intro h0
      have h1 := hz a ha _ (hsb L hL)
      rw [h0, zero_smul] at h1
      have h2 : om (1, a⁻¹) (om (1, a) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)))) =
          C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
          Module.End.one_apply]
      rw [h1, map_zero] at h2
      exact th_phi_ne C Lv hn M hM hM𝔪 v₀ hv B hB L hL h2.symm
    have hep0 : ep 1 ≠ 0 := fun h0 => by
      have := (hep1 L hL).1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hcf0 : cf (gL L) ≠ 0 := fun h0 => by
      have := (hep1 L hL).2.1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hμ0 : μ γ L ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hsc
      have hcf1 : cf (gL (mapL γ L)) ≠ 0 := fun h1 => by
        have := (hep1 _ hL').2.1; rw [h1, norm_zero] at this; exact zero_ne_one this
      have hz1 : z (a₀ * a) ≠ 0 := by
        intro h1
        have h3 := hz _ ha₀a _ (hsb _ hL')
        rw [h1, zero_smul] at h3
        have h2 : om (1, (a₀ * a)⁻¹) (om (1, a₀ * a) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)))) =
            C.Th (C.xB B) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
          rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
            Module.End.one_apply]
        rw [h3, map_zero] at h2
        exact th_phi_ne C Lv hn M hM hM𝔪 v₀ hv B hB _ hL' h2.symm
      exact mul_ne_zero (mul_ne_zero hep0 hcf1) hz1 hsc.symm
    rw [hY]
    have hinv : μ γ L * (μ γ L)⁻¹ = 1 := mul_inv_cancel₀ hμ0
    have hq : z a * ep 1 * cf (gL L) * μ γ L ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hza hep0) hcf0) hμ0
    apply mul_left_cancel₀ hq
    linear_combination (F (mapL γ L) (C.xB (C.mvB (a₀ * a) B))) * hsc - s1 -
      (z a * ep 1 * cf (gL L) * F L (C.xB (C.mvB a B))) * hinv
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.T.domain_frame_eq_real_translate_mul_borel D S T C B hB x hx
  have hxa : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ (hmv a).1).2.1
  have hya : lact γ (C.xB (C.mvB a B)) ∈ C.X.dom := by
    rw [← ((hJ _ (hmv a).1).2.2.2.2.2 γA).2.2.2.2.2 γ hγA, ← (hmv a).2.1 γA]
    exact (hJ _ (hmv _).1).2.1
  rw [lact_rmul, hFb _ hL' _ hya b hb, hFb L hL _ hxa b hb, key a ha]
  ring

end GlobalTheory.Ker.AutRead
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readOffForms_automorphic_inverse_multiplier : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, F (mapL γ L) (lact γ x) = (μ γ L)⁻¹ * F L x := by
  atlas_forward_decl GlobalTheory.Ker.AutRead.read_off_automorphic
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.BddForms

theorem fg_of_mem_lats {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    (Lv : SW.Level X) {L : Lt E r} (hL : L ∈ Lv.lats) : L.FG := by
  obtain ⟨-, s, hcop, hs, -⟩ := hL
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hcop
    have hle := Ideal.mul_le_left (I := Lv.𝔪) (J := conjI Lv.𝔪)
    rw [hcop] at hle
    exact Lv.proper (top_le_iff.1 hle)
  let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := s • LinearMap.id
  have hinj : Function.Injective f := fun v w h => smul_right_injective _ hs0 h
  have hle : L.map f ≤ X.Λ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hs v hv
  have : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
  exact Submodule.fg_of_fg_map_injective f hinj (isNoetherian_submodule.1 this _ hle)

theorem zpow_mul_rpow_sq (t : ℝ) (ht : 0 < t) (l : ℤ) : t ^ l * (t ^ 2) ^ (-(l : ℝ) / 2) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
    Real.rpow_intCast]
  exact mul_inv_cancel₀ (zpow_ne_zero _ ht.ne')

theorem diag_ne_zero {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  obtain ⟨hdet, hlow⟩ := hb τ
  have htri : (mat b τ).BlockTriangular id := fun a c hca => hlow a c hca
  rw [Matrix.det_of_isUpperTriangular htri, Finset.prod_ne_zero_iff] at hdet
  exact hdet i (Finset.mem_univ _)

theorem exists_isSB_ne (n g : ℕ) : ∃ φ : TF n g, SW.IsSB φ ∧ φ ≠ 0 := by
  have key : ∀ x y : Matrix (Fin n) (Fin g) ℚ, SW.IntM y → (SW.IntM (x + y) ↔ SW.IntM x) := by
    intro x y hy
    constructor
    · intro h k i
      simpa using (h k i).sub (hy k i)
    · intro h k i
      simpa using (h k i).add (hy k i)
  have h0 : SW.IntM (0 : Matrix (Fin n) (Fin g) ℚ) := fun k i => by
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℚ))
  refine ⟨fun x => if SW.IntM x then 1 else 0, ⟨1, one_pos, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases h : SW.IntM x
    · simpa using h
    · simp [h] at hx
  · intro x y hy
    simp only [Nat.cast_one, one_smul, key x y hy]
  · intro h
    have := congrFun h 0
    simp [h0] at this

end GlobalTheory.AdSpan.BddForms

namespace GlobalTheory.AdSpan.BddForms

theorem pnorm_le_of_bdd : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  intro D S T C om hW Lv hn M hw hM hMm B hB f' _hbase c c' z φ hz _hγ _hk v₀ μ _hvac _hμ ep cf hepcf gL hgL F
    _hFd hFb hFφ hφb
  obtain ⟨K, hKφ⟩ := hφb
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hmv : ∀ a, C.IsB (C.mvB a B) := fun a => ((hJ B hB).2.2.2.2.2 a).1
  have hdom : ∀ a, C.xB (C.mvB a B) ∈ C.X.dom := fun a => (hJ _ (hmv a)).2.1
  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := exists_isSB_ne S.rank C.g

  have hz1 : ∀ a ∈ GinfC T, ‖z a‖ = 1 := by
    intro a ha
    obtain ⟨c0, hc0, hc0'⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hW 1 (one_mem _) a ha B hB
    have e1 : om (1, a) (C.Th (C.xB B) φ₀) = z a • C.Th (C.xB (C.mvB a B)) φ₀ := hz a ha φ₀ hφ₀
    have e2 := hc0' φ₀ hφ₀
    have : z a = c0 := RealChar.smul_cancel (RealChar.th_ne C (hdom a) hφ₀ hφ₀ne) (e1.symm.trans e2)
    rw [this, hc0]

  have hstdFG : (stdL D.host.E S.rank).FG := Submodule.fg_span (Set.finite_range _)
  have hec : ∀ L ∈ Lv.lats, ‖ep 1 * cf (gL L)‖ = 1 := by
    intro L hL
    obtain ⟨h1, h2, h3⟩ := hgL L hL
    obtain ⟨e1, e2, -⟩ := hepcf 1 (stdL _ _) (gL L) L (one_mem _) (Red.trivAt_one _ _) hstdFG
      (by rw [Red.fmtC_one]; exact Red.isMov_one _) h1 h2 (fg_of_mem_lats Lv hL) h3
    rw [norm_mul, e1, e2, one_mul]

  have hFa : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, ‖F L (C.xB (C.mvB a B))‖ ≤ K := by
    intro L hL a ha
    have h := hKφ (gL L * a)
    rw [hFφ L hL a ha, norm_mul, norm_mul, hz1 a ha, hec L hL, one_mul, one_mul] at h
    exact h
  refine ⟨K, fun L hL x hx => ?_⟩
  obtain ⟨hON, hbB, hxe, hdm, -⟩ := hob x hx
  obtain ⟨a, ha, hax⟩ := (GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved D S T C B hB).2.1 (o x) hON
  have hox : o x ∈ C.X.dom := hax ▸ hdom a
  have hFo : ‖F L (o x)‖ ≤ K := hax ▸ hFa L hL a ha
  set la := wtOf C.X C.hr c c' S.rank with hla
  have hval : F L x = bchar la (b x) * F L (o x) := by
    have := hFb L hL (o x) hox (b x) hbB
    rw [← hxe] at this
    exact this
  have hprod : ‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2) = 1 := by
    unfold bchar
    simp_rw [norm_prod, norm_zpow]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    exact zpow_mul_rpow_sq _ (norm_pos_iff.2 (diag_ne_zero hbB τ i)) _
  simp only [Data.pnorm]
  simp only [← hdm]
  rw [hval, norm_mul]
  calc ‖bchar la (b x)‖ * ‖F L (o x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)
      = ‖F L (o x)‖ * (‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)) := by ring
    _ = ‖F L (o x)‖ := by rw [hprod, mul_one]
    _ ≤ K := hFo

end GlobalTheory.AdSpan.BddForms
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  atlas_forward_decl GlobalTheory.AdSpan.BddForms.pnorm_le_of_bdd
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.EvalAt

theorem theta_eval : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t h Λ hh hht hΛf hhm g L hg hgt hLf hgm a ha Q
  have hΛ0 : C.X.Λ.FG := C.X.Λ_fg
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ hΛ0 hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  have hLl : L ∈ Lv.lats := (hL Lv g L hLf hgm).2.1 hgt
  have hsb : ∀ L ∈ Lv.lats, ∀ Λ ∈ Vset D.host.E S.rank M, SW.IsSB (Lv.phi C.bas hn v₀ L Λ) :=
    fun L hL Λ hΛ => (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      L hL Λ hΛ).1
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hφ0 := hsb _ hΛl _ hstd
  have hφ := hsb L hLl Λ (hV M h Λ hM hht hΛf hhm)
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hth : ∀ B', C.IsB B' → ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsTh (C.Th (C.xB B') φ) :=
    fun B' hB' φ hφ => (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B' hB').2.1 φ hφ).1.1
  have hmv := (hJ B hB).2.2.2.2.2
  have hBa : C.IsB (C.mvB a B) := (hmv a).1
  have hgB : C.mvB g B = B := (hmv g).2.2.1 hg
  have hcomm : a * g = g * a := (((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1 a ha).2.2 g hg
  have p1 : ((h, g * a) : GA D S × GA D T) = (1, a) * (h, g) := by
    rw [Prod.mk_mul_mk, one_mul, hcomm]
  obtain ⟨-, -, e3⟩ := hep h Λ g L hh hht hΛf hhm hg hgt hLf hgm
  rw [(GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ0) Q).2.2.2.2.1, p1, map_mul, Module.End.mul_apply,
    map_smul, GlobalTheory.Ker.Red.om_fvec C om hW h hh g _ (hth B hB _ hφ0) B hB Q, hgB, e3,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) _ (hth B hB _ hφ) Q).2.2.2.2.1, map_smul, map_smul,
    GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) a _ (hth B hB _ hφ) B hB Q, hz a ha _ hφ,
    (GlobalTheory.T.fockPolynomialVector_laws D S T C _ hBa (fun _ => 1) _ (hth _ hBa _ hφ) Q).2.2.2.2.1]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  rw [((GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).2 _ hBa _ hφ).2 Q]
  ring

end GlobalTheory.AdSpan.EvalAt
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_eval_levelTrivial_mul_real : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → ∀ B, C.IsB B → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ z : GA D T → ℂ, (∀ a ∈ GinfC T, RealScal C om B a (z a)) → ∀ (t : ℂ) (h : GA D S) (Λ : Lt D.host.E S.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → ∀ (g : GA D T) (L : Lt D.host.E T.rank), g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ∀ a ∈ GinfC T, ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, om (h, g * a) (C.fvec B (t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) Q) 0 = t * ep h * cf g * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L Λ) (C.toH Q) (C.xB (C.mvB a B)) := by
  atlas_forward_decl GlobalTheory.AdSpan.EvalAt.theta_eval
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_group_congruent_of_two_lattice_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ L → C.LevK Lv (g₁⁻¹ * g₂) 1 := by
  first | exact @GlobalTheory.Ker.LevMove.levK_of_two_moves | exact GlobalTheory.Ker.LevMove.levK_of_two_moves | (intros; apply GlobalTheory.Ker.LevMove.levK_of_two_moves <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ExtInv

theorem eq_of_invariant : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (M : ℕ), 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ φ ψ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g) → (∀ k, C.LevK Lv k 1 → ∀ g, φ (g * k) = φ g) → (∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)) → φ = ψ := by
  intro D S T C Lv M hM hM𝔪 gL hgL φ ψ hφ hψ hφk hψk hag
  have hΛ : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [Red.fmt_one]; exact Red.isMov_one _
  obtain ⟨-, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hI : C.under Lv ≠ ⊥ := (hL Lv 1 _ hΛ.1 hm1).2.2.1
  have hgrp := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.1
  have hcomm := ((GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T).2.2.2.1
  funext g
  obtain ⟨γ, hγ, a, ha, g', hg', k, hk, hg, ht, -, hck, hcJ⟩ := GlobalTheory.T.exists_rational_real_trivialAt_congruent_factor D T C.X.Λ (C.under Lv) M hΛ hI hM g
  have hinv : fmt T g' * fmt T g'⁻¹ = 1 := by rw [← (hgrp g' g'⁻¹).2.1, mul_inv_cancel, Red.fmt_one]
  obtain ⟨L, hLf, hLm⟩ := ((GlobalTheory.T.finiteAdelicLatticeTransport_laws D _ C.X.Λ hΛ).2.2.2 _ _ hinv).1
  have hLl : L ∈ Lv.lats := (hL Lv g' L hLf.1 hLm).2.1 ht
  obtain ⟨h1, h2, h3⟩ := hgL L hLl
  have hk1 : C.LevK Lv k 1 := Red.levK_one C Lv k hk hck.1 (hcJ _ hM𝔪)
  have hk2 : C.LevK Lv ((gL L)⁻¹ * g') 1 := GlobalTheory.T.level_group_congruent_of_two_lattice_moves D S T C Lv (gL L) g' L h1 hg' h2 ht hLf.1 h3 hLm
  have e : g = γ * (gL L * a * ((gL L)⁻¹ * g') * k) := by
    rw [hg, ← (hcomm a ha).2.2 _ h1]
    group
  rw [e, hφ γ hγ, hψ γ hγ, hφk k hk1, hψk k hk1, hφk _ hk2, hψk _ hk2]
  exact hag L hLl a ha

end GlobalTheory.Ker.ExtInv
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_rational_level_invariant_agree_chosen : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (M : ℕ), 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ φ ψ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g) → (∀ k, C.LevK Lv k 1 → ∀ g, φ (g * k) = φ g) → (∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)) → φ = ψ := by
  atlas_forward_decl GlobalTheory.Ker.ExtInv.eq_of_invariant
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.ThInv

theorem fvec_val_inv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (h : GA D S) (B : C.Bas), C.IsB B → ∀ u : WO S T → ℂ, C.IsTh u → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, (∀ γ ∈ GQ T, ∀ g, om (h, γ * g) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) ∧ ((∀ k, C.LevK Lv k 1 → om (1, k) u = u) → ∀ k, C.LevK Lv k 1 → ∀ g, om (h, g * k) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) := by
  intro D S T C om hW Lv h B hB u hu Q
  have hth : C.IsTh (C.fvec B u Q) := (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u hu Q).1
  refine ⟨fun γ hγ g => ?_, fun hk k hkL g => ?_⟩
  · have p : ((h, γ * g) : GA D S × GA D T) = (1, γ) * (h, g) := by
      rw [Prod.mk_mul_mk, one_mul]
    rw [p, map_mul, Module.End.mul_apply]
    exact hW.om_aut 1 (one_mem _) γ hγ _ (hW.om_pres _ _ hth)
  · have p : ((h, g * k) : GA D S × GA D T) = (h, g) * (1, k) := by
      rw [Prod.mk_mul_mk, mul_one]
    have hmv := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.2.2.2.2 k
    rw [p, map_mul, Module.End.mul_apply, GlobalTheory.Ker.Red.om_fvec C om hW 1 (one_mem _) k u hu B hB Q,
      hmv.2.2.1 hkL.1, hk k hkL]

end GlobalTheory.Ker.ThInv
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_fock_vector_invariance : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (h : GA D S) (B : C.Bas), C.IsB B → ∀ u : WO S T → ℂ, C.IsTh u → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, (∀ γ ∈ GQ T, ∀ g, om (h, γ * g) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) ∧ ((∀ k, C.LevK Lv k 1 → om (1, k) u = u) → ∀ k, C.LevK Lv k 1 → ∀ g, om (h, g * k) (C.fvec B u Q) 0 = om (h, g) (C.fvec B u Q) 0) := by
  atlas_forward_decl GlobalTheory.Ker.ThInv.fvec_val_inv
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  intro D S T C om hW hsz Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hhol hγ hk hbdd
  obtain ⟨v₀, μ, hv, hμ⟩ := GlobalTheory.SW.exists_vacua_and_multipliers D.host.E T.rank C.X C.g C.bas C.idx S.rank
    C.sympl C.even Lv
  obtain ⟨ep, cf, hep⟩ := GlobalTheory.T.weilPair_levelTrivial_maps_levelVector D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ C.X.Λ_fg hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  obtain ⟨t, ht0, hft⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase (v₀ C.X.Λ) (hv _ hΛl)
  have hu : C.uVec Lv hn f' = t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    rw [hft]; exact ((GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv).2 t
  have hex : ∀ L : Lt D.host.E T.rank, ∃ g : GA D T, L ∈ Lv.lats →
      g ∈ GfC T ∧ TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
    intro L
    by_cases hL' : L ∈ Lv.lats
    · obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.Ker.OntoLat.exists_trivAt_mov D S T C Lv L hL'
      exact ⟨g, fun _ => ⟨hg, h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hL'⟩
  choose gL hgL using hex
  choose Qf hQd hQb hQv using fun L => hhol (gL L)
  have hne : ∀ L ∈ Lv.lats, ep 1 * cf (gL L) ≠ 0 := by
    intro L hL'
    obtain ⟨g1, g2, -⟩ := hep 1 _ (gL L) L (one_mem _) (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
      (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2
    refine mul_ne_zero ?_ ?_ <;> intro h0
    · rw [h0, norm_zero] at g1; exact zero_ne_one g1
    · rw [h0, norm_zero] at g2; exact zero_ne_one g2
  let F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ := fun L x => Qf L x / (ep 1 * cf (gL L))
  have hFhol : ∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom := fun L _ => by
    show DifferentiableOn ℂ (fun x => Qf L x / (ep 1 * cf (gL L))) C.X.dom
    simpa only [div_eq_mul_inv] using (hQd L).mul_const (ep 1 * cf (gL L))⁻¹
  have hFbor : ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank,
      F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x := by
    intro L _ x hx b hb
    show Qf L (rmul x b) / _ = _ * (Qf L x / _)
    rw [hQb L x hx b hb, mul_div_assoc]
  have hFv : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T,
      φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B)) := by
    intro L hL' a ha
    show _ = _ * (Qf L _ / _)
    rw [hQv L a ha, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (hne L hL')]
  have hForm : IsForm C.X Lv.grp Lv.lats μ (wtOf C.X C.hr c c' S.rank) F :=
    ⟨hFhol, hFbor, GlobalTheory.T.readOffForms_automorphic_inverse_multiplier D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv,
     GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv hbdd⟩
  obtain ⟨m, Λs, P, a, hΛP, hsp⟩ := GlobalTheory.SW.level_theta_span D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx
    S.rank C.sympl C.even hsz Lv hn M hM hM𝔪 v₀ hv μ hμ c c' F hForm
  choose hs hsf hst hsm using fun i => GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual D S T C M hM (Λs i) (hΛP i).1
  have hbij := (GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).1
  let Qs : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ := fun i => Function.surjInv hbij.2 (P i)
  have hQs : ∀ i, C.toH (Qs i) = P i := fun i => Function.surjInv_eq hbij.2 (P i)
  have hepn : ∀ i, ep (hs i) ≠ 0 := by
    intro i h0
    obtain ⟨g1, -⟩ := hep (hs i) (Λs i) 1 C.X.Λ (hsf i) (hst i) (hΛP i).1.1 (hsm i) (one_mem _)
      (GlobalTheory.Ker.Red.trivAt_one _ _) C.X.Λ_fg hm1
    rw [h0, norm_zero] at g1; exact zero_ne_one g1
  let Θ : Fin m → GA D T → ℂ := fun i g => om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0
  let ψ : GA D T → ℂ := ∑ i, (a i * ep 1 / (t * ep (hs i))) • Θ i
  have hψ : ∀ g, ψ g = ∑ i, (a i * ep 1 / (t * ep (hs i))) * Θ i g := by
    intro g; simp only [ψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hψmem : ψ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨hs i, Qs i, by rw [hQs i]; exact (hΛP i).2, rfl⟩)
  suffices hφψ : φ = ψ by rw [hφψ]; exact hψmem
  set u0 := C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) with hu0
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hth0 : C.IsTh u0 := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B hB).2.1 _
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      C.X.Λ hΛl _ hstd).1).1.1
  have hΘ : ∀ i g, Θ i g = t * om (hs i, g) (C.fvec B u0 (Qs i)) 0 := by
    intro i g
    show om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0 = _
    rw [hu, (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u0 hth0 (Qs i)).2.2.2.2.1 t, map_smul, Pi.smul_apply,
      smul_eq_mul]
  have hk0 : ∀ k, C.LevK Lv k 1 → om (1, k) u0 = u0 := by
    intro k hk'
    have e := (hk k 1 hk').1
    rw [hu, map_smul] at e
    exact smul_right_injective _ ht0 e
  have hinv := fun i => GlobalTheory.T.theta_series_fock_vector_invariance D S T C om hW Lv (hs i) B hB u0 hth0 (Qs i)
  have hψγ : ∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g := by
    intro γ hγ' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).1 γ hγ' g]
  have hψk : ∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g := by
    intro k hk' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).2 hk0 k hk' g]
  have hag : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a) := by
    intro L hL' a ha
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ ((hJ B hB).2.2.2.2.2 a).1).2.1
    have hev : ∀ i, Θ i (gL L * a) = t * ep (hs i) * cf (gL L) * z a *
        thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L (Λs i)) (P i) (C.xB (C.mvB a B)) := by
      intro i
      show om _ (C.fvec B (C.uVec Lv hn f') _) 0 = _
      rw [hu, GlobalTheory.T.thetaSeries_eval_levelTrivial_mul_real D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t (hs i) (Λs i) (hsf i) (hst i)
        (hΛP i).1.1 (hsm i) (gL L) L (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2 a ha (Qs i), hQs i]
    rw [hFv L hL' a ha, hψ, hsp L hL' _ hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i]
    have h1 := hepn i
    field_simp
  exact GlobalTheory.T.eq_of_rational_level_invariant_agree_chosen D S T C Lv M hM hM𝔪 gL hgL φ ψ hγ hψγ (fun k hk' => (hk k 1 hk').2) hψk hag
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_thetaSeries_of_boundedHolomorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  atlas_forward_decl GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo
end
