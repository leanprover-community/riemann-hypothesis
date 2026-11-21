import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPurePairIffMonodromyFiltration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedWeightSpaceBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneWeightSpaceStable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightFiltrationStrandDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveStrandComplementLefschetz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneDirectSumOfCompl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedTopWeightStrand
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedOfTemperedLpSum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentUnitarisableTwist

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.WeilDeligne.TemperedCharPol

open GlobalTheory.WeilDeligne.PrimDecomp Module

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem map_wtSpace {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (e : V ≃ₗ[ℂ] V') (he : ∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) (k : ℤ) :
    (wtSpace a k).map (e : V →ₗ[ℂ] V') = wtSpace b k := by
  apply le_antisymm
  · exact map_absSpace_le e.toLinearMap (he (frob h)) _
  · intro v hv
    refine ⟨e.symm v, ?_, by simp⟩
    exact (mem_absSpace_iff e (he (frob h)) _ (e.symm v)).mp (by rw [LinearEquiv.apply_symm_apply]; exact hv)

theorem isCompl_of_tempered {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (ha : a.Tempered) (m : ℕ) (hmtop : ∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) :
    IsCompl (strand a.N (wtSpace a (-(m : ℤ))) m) (lowPart (wtSpace a) a.N m) := by
  obtain ⟨-, hNk⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ a
  have hpure := ha (frob h) deg_frob
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 := zero_lt_one.trans hq
  have hind : iSupIndep (wtSpace a) := by
    refine iSupIndep_absSpace _ fun i j hij => ?_
    rw [Real.rpow_right_inj hq0 hq.ne'] at hij
    exact_mod_cast (by linarith : (i : ℝ) = j)
  have htop : ⨆ i, wtSpace a i = ⊤ := hpure.1
  have hbij : ∀ i : ℕ, Set.BijOn (a.N ^ i) (wtSpace a (-(i : ℤ))) (wtSpace a i) := by
    intro i
    simp only [wtSpace, Int.cast_neg, Int.cast_natCast]
    exact hpure.2 i
  exact GlobalTheory.T.primitive_strand_complement_lefschetz _ (wtSpace a) a.N m hind htop hNk hbij hmtop

theorem step {d : ℕ}
    (ih : ∀ x y : WD h, x.lpDim < d → x.tempered → y.tempered → (∀ g, x.charPol g = y.charPol g) → x = y)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h V')
    (hd : finrank ℂ V = d) (ha : a.Tempered) (hb : b.Tempered)
    (e : V ≃ₗ[ℂ] V') (he : ∀ σ v, e (a.ρ σ v) = b.ρ σ (e v)) : WD.mk a = WD.mk b := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact WD.sound ⟨e, he, fun v => by rw [Subsingleton.elim v 0]; simp⟩
  obtain ⟨m, hm0, hmtop⟩ := GlobalTheory.T.tempered_weight_space_bound E Ω A w h V a ha hV
  have hmap := map_wtSpace a b e he
  have hmtop' : ∀ k : ℤ, (m : ℤ) < k → wtSpace b k = ⊥ := fun k hk => by
    rw [← hmap, hmtop k hk, Submodule.map_bot]
  obtain ⟨hρa, hNa⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ a
  obtain ⟨hρb, hNb⟩ := GlobalTheory.T.weil_deligne_weight_space_stable E Ω A w h _ b
  obtain ⟨hBa, hCa⟩ := GlobalTheory.T.weight_filtration_strand_decomposition E Ω A w h _ a m hρa hNa hmtop
  obtain ⟨hBb, hCb⟩ := GlobalTheory.T.weight_filtration_strand_decomposition E Ω A w h _ b m hρb hNb hmtop'
  have e1a := GlobalTheory.T.weil_deligne_direct_sum_of_compl E Ω A w h _ a _ _ hBa hCa (isCompl_of_tempered a ha m hmtop)
  have e1b := GlobalTheory.T.weil_deligne_direct_sum_of_compl E Ω A w h _ b _ _ hBb hCb (isCompl_of_tempered b hb m hmtop')
  have e2a := GlobalTheory.T.tempered_top_weight_strand E Ω A w h _ a m (fun σ v hv => hρa _ σ v hv) hBa ha hmtop
  have e2b := GlobalTheory.T.tempered_top_weight_strand E Ω A w h _ b m (fun σ v hv => hρb _ σ v hv) hBb hb hmtop'

  have hy : WD.mk (restrictρ a (wtSpace a (-(m : ℤ))) (fun σ v hv => hρa _ σ v hv)) =
      WD.mk (restrictρ b (wtSpace b (-(m : ℤ))) (fun σ v hv => hρb _ σ v hv)) := by
    refine WD.sound ⟨(e.submoduleMap (wtSpace a (-(m : ℤ)))).trans (LinearEquiv.ofEq _ _ (hmap _)),
      fun σ v => ?_, fun v => ?_⟩
    · apply Subtype.ext
      simp [he]
    · simp
  have hB : WD.mk (restrict a _ hBa) = WD.mk (restrict b _ hBb) := by rw [e2a, e2b, hy]

  have hcC : ∀ g, (WD.mk (restrict a _ hCa)).charPol g = (WD.mk (restrict b _ hCb)).charPol g := by
    intro g
    have hab : (WD.mk a).charPol g = (WD.mk b).charPol g := by
      rw [WD.charPol_mk, WD.charPol_mk, ← LinearEquiv.charpoly_conj e]
      congr 1
      ext v
      simp [LinearEquiv.conj_apply, he]
    rw [e1a, e1b, WD.charPol_lpSum, WD.charPol_lpSum, hB] at hab
    exact mul_left_cancel₀ (WD.charPol_monic _ g).ne_zero hab
  have htC : (WD.mk (restrict a _ hCa)).tempered :=
    GlobalTheory.T.tempered_of_tempered_lpSum' E Ω A w h _ _ (by rw [← e1a, WD.tempered_mk]; exact ha)
  have htC' : (WD.mk (restrict b _ hCb)).tempered :=
    GlobalTheory.T.tempered_of_tempered_lpSum' E Ω A w h _ _ (by rw [← e1b, WD.tempered_mk]; exact hb)
  have hdim : (WD.mk (restrict a _ hCa)).lpDim < d := by
    have h1 := congrArg WD.lpDim e1a
    rw [WD.lpDim_sum, WD.lpDim_mk, hd] at h1
    have hUpos : 0 < finrank ℂ (wtSpace a (-(m : ℤ))) :=
      Nat.pos_of_ne_zero fun h0 => hm0 (Submodule.finrank_eq_zero.mp h0)
    have hBpos : 0 < (WD.mk (restrict a _ hBa)).lpDim := by
      rw [WD.lpDim_mk]
      exact hUpos.trans_le (Submodule.finrank_mono (le_strand _ _ _))
    omega
  rw [e1a, e1b, hB, ih _ _ hdim htC htC' hcC]

theorem main : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (∀ g : Weil h, x.charPol g = y.charPol g) → x = y := by
  intro E Ω _ _ _ _ _ A w h
  have key : ∀ d : ℕ, ∀ x y : WD h, x.lpDim = d → x.tempered → y.tempered →
      (∀ g, x.charPol g = y.charPol g) → x = y := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro x y hxd hx hy hc
      induction x using WD.ind with
      | hP n a =>
      induction y using WD.ind with
      | hP n' b =>
      rw [WD.tempered_mk] at hx hy
      rw [WD.lpDim_mk] at hxd
      obtain ⟨e, he⟩ := GlobalTheory.AboveL.weil_rep_equiv_of_charpoly_eq E Ω A w h n n' a b
        (fun σ => by rw [← WD.charPol_mk, ← WD.charPol_mk]; exact hc σ)
      exact step (fun x y hxy => ih _ hxy x y rfl) a b hxd hx hy e he
  exact fun x y => key _ x y rfl

end GlobalTheory.WeilDeligne.TemperedCharPol
end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

noncomputable section

namespace GlobalTheory.GalCut.AwayMono

open Polynomial

theorem charpoly_smul_scaleRoots {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {c : ℂ} (hc : c ≠ 0) : (c • f).charpoly = f.charpoly.scaleRoots c := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul,
    ← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  generalize LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f = M
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpTw (x : WD h) (s : ℝ) (g : Weil h) :
    (x.lpTw s).charPol g = (x.charPol g).scaleRoots (unrChar h (qPow w s) g : ℂ) := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTw, WD.lpTwist_mk, WD.charPol_mk, WD.charPol_mk, WDRep.twist_ρ,
    charpoly_smul_scaleRoots _ (Units.ne_zero _)]

theorem charPol_lpTw_congr {x y : WD h} (H : ∀ g, x.charPol g = y.charPol g) (s : ℝ) (g : Weil h) :
    (x.lpTw s).charPol g = (y.lpTw s).charPol g := by
  rw [charPol_lpTw, charPol_lpTw, H]

theorem isGeneric_nu {x : IrrGL (w.adicCompletion E)} (hx : IsGeneric x.rep) (s : ℂ) : IsGeneric (x.nu s).rep :=
  (isGeneric_congr (IrrGL.twEquiv x _ _)).1 ((isGeneric_twist_iff _).2 hx)

end GlobalTheory.GalCut.AwayMono

end
end
