import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAtMove
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TupleMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFramesDoublingPolynomialExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTowerFrameCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKIntMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolIntegrableOnIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypotheses
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralsPositionOneEqCellSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceOffTypePrimeDescription
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.XiAway

theorem xi_awayIm : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ t : T, LocIn D.what₂.embLL (L.xiH t) →
      ∀ (m : ℕ) (y : (AE D)ˣ), GlobalTheory.KappaArith.AwayIm D m ((L.xi t y : Circle) : ℂ) := by
  intro D T L μ₀ hL t hx m y
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h := hL.xi t
  have h1 : L.xi t y ^ n = 1 := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (L.xi t ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D _ _ h n ho) y
  obtain ⟨ζ, hζ⟩ := GlobalTheory.TwistValues.char_mem (L.xi t) (L.xiH t) h hn ho D.what₂.embLL.fieldRange
    (fun P k => hx P (Formalism.L2.Host.atFin P k)) y
  have h2 : ζ ^ n = 1 := D.what₂.embLL.injective (by
    rw [map_pow, map_one]
    erw [hζ]
    have := congrArg (fun w : Circle => (w : ℂ)) h1
    simpa using this)
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hn h2, hζ⟩

end GlobalTheory.XiAway
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

open Formalism.L2.Host (HChar)

namespace GlobalTheory.TopFlipNu

theorem exists_pow_close {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x c : w.adicCompletion E)
    (hx : Valued.v x = 1) (hc : c ≠ 0) : ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have e := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hK : IsCompact {y : w.adicCompletion E | Valued.v y ≤ 1} := by
    have := IsNonarchimedeanLocalField.isCompact_closedBall (w.adicCompletion E) 1
    convert this using 1
    ext y
    exact e.le_one_iff_le_one.symm
  have hv0 : Valued.v c ≠ 0 := by simpa using hc
  obtain ⟨s, -, hs⟩ := hK.elim_nhds_subcover (fun y => {z | (z - y) * c⁻¹ ∈ w.adicCompletionIntegers E}) fun y _ =>
    ((Valued.isOpen_valuationSubring _).preimage ((continuous_id.sub continuous_const).mul continuous_const)).mem_nhds
      (by simp)
  have h1 : ∀ n : ℕ, ∃ y : s, Valued.v (x ^ n - y) ≤ Valued.v c := fun n => by
    have : x ^ n ∈ {y : w.adicCompletion E | Valued.v y ≤ 1} := by simp [hx]
    obtain ⟨y, hy, h⟩ := Set.mem_iUnion₂.1 (hs this)
    refine ⟨⟨y, hy⟩, ?_⟩
    have h2 : Valued.v ((x ^ n - y) * c⁻¹) ≤ 1 := h
    rwa [map_mul, map_inv₀, mul_inv_le_iff₀ (zero_lt_iff.2 hv0), one_mul] at h2
  choose f hf using h1
  have key : ∀ a b : ℕ, a < b → f a = f b → ∃ k : ℕ, 0 < k ∧ Valued.v (x ^ k - 1) ≤ Valued.v c := fun a b hab h => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    refine ⟨k + 1, by omega, ?_⟩
    have h3 := Valuation.map_sub_le _ (hf (a + k + 1)) (h ▸ hf a)
    have h4 : x ^ (a + k + 1) - f (a + k + 1) - (x ^ a - f (a + k + 1)) = x ^ a * (x ^ (k + 1) - 1) := by ring
    rwa [h4, map_mul, map_pow, hx, one_pow, one_mul] at h3
  obtain ⟨a, b, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hne with h' | h'
  exacts [key a b h' h, key b a h' h.symm]

theorem exists_pow_eq_one {E : Type} [Field E] [NumberField E] {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion E)ˣ) (hx : Valued.v (x : w.adicCompletion E) = 1) :
    ∃ k : ℕ, 0 < k ∧ χ.loc w x ^ k = 1 := by
  have hu := Formalism.L2.Host.unif_spec w
  unfold Formalism.L2.Host.IsUnifAt at hu
  obtain ⟨k, hk, h1⟩ := exists_pow_close w x
    (((Formalism.L2.Host.atFin w (Formalism.L2.Host.unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) ^ n) hx
    (pow_ne_zero _ (Units.ne_zero _))
  refine ⟨k, hk, ?_⟩
  rw [← map_pow]
  refine h _ ?_ ?_
  · show Valued.v _ = 1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  · rw [map_pow, hu, ← WithZero.exp_nsmul] at h1
    rw [Units.val_pow_eq_pow_val]
    simpa using h1

theorem awayIm_unit {D : D7} {χ : HChar D.host.E} (hχ : LocIn D.what₂.embLL χ) {w : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : χ.LevelLe w n) (x : (w.adicCompletion D.host.E)ˣ) (hx : Valued.v (x : w.adicCompletion D.host.E) = 1) (m : ℕ) :
    GlobalTheory.KappaArith.AwayIm D m (χ.loc w x : ℂ) := by
  obtain ⟨k, hk, h1⟩ := exists_pow_eq_one h x hx
  obtain ⟨ζ, hζ⟩ := hχ w x
  have h2 : ζ ^ k = 1 := D.what₂.embLL.injective (by rw [map_pow, hζ, map_one, ← Units.val_pow_eq_pow_val, h1, Units.val_one])
  exact ⟨ζ, GlobalTheory.KappaArith.isAwayUnit_of_pow_eq_one m hk h2, hζ⟩

theorem chi_levelLe {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) : (G.ch.chiH i).LevelLe w 2 := by
  by_cases h : w.under (𝓞 D.host.F) ∈ G.pl.S0
  · rcases G.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact fun x hx h3 => (G.ch.lev0 i h1 h2 w h).1 x hx (h3.trans (WithZero.exp_le_exp.2 (by omega)))
    · exact (G.ch.lev1 i h1 h2 w h).1
  · exact fun x hx _ => G.ch.unr i h1 h2 w h x hx

theorem nu_arith : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → CharsIn G D.what₂.embLL → ∀ (i j : Fin D.R.m) (x : ∀ w : Pl D.host.E, (Kw w)ˣ) (t : T),
      (∀ w ∈ locPl G t, ValuativeRel.valuation (Kw w) (x w : Kw w) = 1) →
      ∃ z : ℂ, GlobalTheory.KappaArith.AwayIm D (Qn G t) z ∧ ∏ w ∈ locPl G t, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
        z * ∏ w ∈ locPl G μ₀, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := by
  classical
  intro D T L sc G μ₀ hL hC i j x t hx
  have hQ : L.Q μ₀ = ∅ := Finset.eq_empty_of_forall_notMem fun w hw =>
    (hL.Q_ram μ₀ w).2 (Or.inl hw) (by rw [hL.xi_base]; intro x _; rfl)
  have h0 : locPl G μ₀ = G.pl.W0 := by rw [locPl, hQ]; simp
  have hsub : G.pl.W0 ⊆ locPl G t := fun w hw => by unfold locPl; simp [hw]
  have hf : ∀ w, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) =
      ((L.xiH t).loc w (x w) : ℂ) * (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w => by
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, Formalism.L2.Host.HChar.loc_mul, hL.xi_base, Formalism.L2.Host.HChar.loc_one,
      Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
    ring
  have hb : ∀ w ∈ locPl G t, GlobalTheory.KappaArith.AwayIm D (Qn G t) (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ) := fun w hw => by
    haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
    have e := ValuativeRel.isEquiv (ValuativeRel.valuation (Kw w)) (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ)))
    have hv : Valued.v (x w : Kw w) = 1 := e.eq_one_iff_eq_one.1 (hx w hw)
    have hv' : Valued.v (((x w)⁻¹ : (Kw w)ˣ) : Kw w) = 1 := by rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
    have a := awayIm_unit (hC.mu0 j) ((L.C.isMu0 j).tame w) (x w) hv (Qn G t)
    have b := awayIm_unit (hC.chi _ h1 h2) (chi_levelLe G h1 h2 w) (x w)⁻¹ hv' (Qn G t)
    have hm : muBase L (j + 1) = L.C.mu0 j := by rw [muBase, dif_pos j.2]
    convert a.mul b using 1
    simp only [Grid.nu, locGrid, MonoidHom.div_apply, hL.xi_base, mul_one, hm, map_inv,
      Units.val_div_eq_div_val, Units.val_inv_eq_inv_val]
    exact div_eq_mul_inv _ _
  refine ⟨(∏ w ∈ locPl G t, ((L.xiH t).loc w (x w) : ℂ)) *
    ∏ w ∈ locPl G t \ G.pl.W0, (((locGrid G μ₀ w).nu i j (x w) : ℂˣ) : ℂ), ?_, ?_⟩
  · exact (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w _ => GlobalTheory.KappaArith.awayIm_val hL (hC.xi t) _ w (x w)).mul
      (GlobalTheory.KappaArith.AwayIm.prod _ _ fun w hw => hb w (Finset.mem_sdiff.1 hw).1)
  · rw [h0, mul_assoc, Finset.prod_sdiff hsub, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun w _ => hf w

end GlobalTheory.TopFlipNu
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.TopFlip.MeasW

theorem nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {t t' : T} {M M' : Vol G}
    (hM : M.Is t) (hM' : M'.Is t') (i j : Fin D.R.m) :
    M.ν (.grid (i + 1) (j + 1)) = M'.ν (.grid (i + 1) (j + 1)) :=
  GlobalTheory.FunObjModel.isAt_unique (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩) (hM'.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩)

theorem exists_ratio : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (i j : Fin D.R.m) (m : Measure (GA D (spW G i j))), m.IsHaarMeasure →
      ∃ s₀ : NNReal, s₀ ≠ 0 ∧ ∀ (t : T) (M : Vol G), M.Is t → ∀ s : NNReal, M.ν (.grid (i + 1) (j + 1)) = s • m → s = s₀ := by
  intro D T L sc G μ₀ _ i j m hm
  by_cases h : ∃ (t : T) (M : Vol G) (s : NNReal), M.Is t ∧ M.ν (.grid (i + 1) (j + 1)) = s • m
  · obtain ⟨t₀, M₀, s₀, hM₀, e₀⟩ := h
    have hH := (hM₀.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund.1
    obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (spW G i j)
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (GA D (spW G i j))) := inferInstance
    have hK0 : m K ≠ 0 :=
      ((isOpen_interior.measure_pos m K.interior_nonempty).trans_le (measure_mono interior_subset)).ne'
    have hK1 : m K ≠ ⊤ := K.isCompact.measure_lt_top.ne
    refine ⟨s₀, ?_, fun t M hM s e => ?_⟩
    · rintro rfl
      rw [e₀, zero_smul] at hH
      exact (isOpen_univ.measure_pos (0 : Measure (GA D (spW G i j))) Set.univ_nonempty).ne' rfl
    · have e1 : s • m = s₀ • m := e.symm.trans ((nu_eq hM hM₀ i j).trans e₀)
      have e2 : (s : ENNReal) * m K = (s₀ : ENNReal) * m K := by
        have e3 := congrArg (fun μ : Measure (GA D (spW G i j)) => μ K) e1
        exact e3
      exact_mod_cast (ENNReal.mul_left_inj hK0 hK1).1 e2
  · exact ⟨1, one_ne_zero, fun t M hM s e => absurd ⟨t, M, s, hM, e⟩ h⟩

end GlobalTheory.TopFlip.MeasW

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip
open ValuativeRel
open scoped NNReal ENNReal

noncomputable section

namespace GlobalTheory.TopFlip.MeasLevel

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vol_mul_relIndex [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (J : Subgroup (GL n k))
    (ho : IsOpen (J : Set (GL n k))) (hle : J ≤ KO k n) :
    (haarVol (KO k n)).real (J.map invT : Subgroup _) * (J.relIndex (KO k n) : ℝ) = 1 := by
  obtain ⟨ho', hle'⟩ := isOpen_map_invT ho hle
  have hK : (KO k n).map invT = KO k n := by
    refine le_antisymm ?_ fun g hg => ⟨invT g, invT_mem_KO hg, GlobalTheory.SplitFlip.invT_invT g⟩
    rintro _ ⟨g, hg, rfl⟩
    exact invT_mem_KO hg
  have hinj : Function.Injective (invT : GL n k →* GL n k) := Function.LeftInverse.injective GlobalTheory.SplitFlip.invT_invT
  have hi : (J.map invT).relIndex (KO k n) = J.relIndex (KO k n) := by
    conv_lhs => rw [← hK]
    exact Subgroup.relIndex_map_map_of_injective _ _ hinj
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  have ho2 : IsOpen (((J.map invT).subgroupOf (KO k n) : Subgroup (KO k n)) : Set (KO k n)) :=
    ho'.preimage continuous_subtype_val
  haveI : Finite (KO k n ⧸ (J.map invT).subgroupOf (KO k n)) := Subgroup.quotient_finite_of_isOpen _ ho2
  haveI : ((J.map invT).subgroupOf (KO k n)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h := GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup _ (KO k n) hle' ho'.measurableSet (haarVol (KO k n))
  rw [haarVol_self GlobalTheory.SplitFlip.isOpen_KO le_rfl, hi] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_one, mul_comm] at h2
  exact h2

theorem gl_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Function.Surjective (GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  choose f hf using (IsLocalRing.residue_surjective (R := O))
  have hM : (IsLocalRing.residue O).mapMatrix (g.val.map f) = g.val := by
    ext a b
    simp [hf]
  have hd : IsUnit (g.val.map f).det := by
    refine (isUnit_map_iff (IsLocalRing.residue O) _).1 ?_
    rw [RingHom.map_det, hM]
    exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨u, Units.ext ?_⟩
  rw [← hM, ← hu]
  rfl

theorem relIndex_parahoric {n : ℕ} (r : ℕ) (J : Subgroup (GL (Fin n) k))
    (hJ : ∀ g, g ∈ J ↔ g ∈ KO k (Fin n) ∧ ∀ a b, blk2 r b < blk2 r a → valuation k (g.1 a b) < 1) :
    J.relIndex (KO k (Fin n)) = (blockTri (blk2 r) : Subgroup (GL (Fin n) 𝓀[k])).index := by
  have e : J.comap (GeneralLinearGroup.map (n := Fin n) (algebraMap (valuation k).integer k)) =
      (blockTri (blk2 r) : Subgroup (GL (Fin n) 𝓀[k])).comap
        (GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue (valuation k).integer)) := by
    ext g
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hJ, mem_blockTri]
    have key : ∀ x : (valuation k).integer, IsLocalRing.residue (valuation k).integer x = 0 ↔ valuation k (x : k) < 1 :=
      fun x => by
        rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    refine ⟨fun h a b hab => (key _).2 (h.2 a b hab), fun h => ⟨⟨g, rfl⟩, fun a b hab => (key _).1 (h a b hab)⟩⟩
  rw [KO, ← Subgroup.index_comap, e, Subgroup.index_comap_of_surjective _ (gl_residue_surjective _ n)]

end Local

variable {D : D7}

theorem index_residue (w : Pl D.host.E) {n n' r s : ℕ} (h : n = r + s) (h' : n' = r + s) :
    ((blockTri (blk2 r) : Subgroup (GL (Fin n) 𝓀[Kw w])).index : ℝ) =
      (blockTri (blk2 r) : Subgroup (GL (Fin n') (kP w))).index := by
  letI : Field (kP w) := Ideal.Quotient.field _
  have hq : Nat.card (kP w) = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq' : Nat.card 𝓀[Kw w] = Ideal.absNorm w.asIdeal :=
    GlobalTheory.LocalResidue.card_residue_of_ringEquiv D.host.E w (Kw w) (RingEquiv.refl _) fun a =>
      (GivenAdm.isEquiv_val w).le_one_iff_le_one.symm
  refine (GlobalTheory.ParabIndex.index_maxParabolic_GL_finiteField 𝓀[Kw w] n r s h).trans
    (Eq.trans ?_ (GlobalTheory.ParabIndex.index_maxParabolic_GL_finiteField (kP w) n' r s h').symm)
  rw [hq, hq', h, h']

open Classical in

theorem relIndex_lev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    (hN : Lev.IsBaseFrame V β Λ N) {r t j : ℕ} (hr : r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (hnc : ∀ P ∈ Pg ∪ Q, ∀ P' ∈ Pg ∪ Q, ¬ Lev.IsConjPl P P') (hd : Disjoint Pg Q)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ≤
      lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) ∧
    (lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B)).relIndex
      (lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B)) =
      ∏ PP ∈ Q, (blockTri (blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))).index := by
  have hmem := fun x => GlobalTheory.TwistIndex.mem_datY_iff V β hr hr Pg Q χ χ ξ ξ' (r := r) (t := t) (j := j) x
  refine ⟨fun x hx => ((hmem x).1 hx).1, ?_⟩
  have hSt : lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) ≤
      St β := fun x hx => parLev_St hx.1
  let φ : lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) →*
      (∀ PP : Q, GL (Fin V.rank) (kP PP.1)) :=
    MonoidHom.pi fun PP => (redAt β PP.1).comp (Subgroup.inclusion hSt)
  have hφ : ∀ x PP, φ x PP = redFn β PP.1 x.1 := by
    intro x PP
    unfold redFn
    rw [extendOne_of_mem _ (hSt x.2)]
    rfl
  have hcomap : (lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B)).subgroupOf
      (lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B)) =
      (Subgroup.pi Set.univ fun PP : Q =>
        (blockTri (blk2 r) : Subgroup (GL (Fin V.rank) (kP PP.1)))).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hmem]
    simp only [hφ]
    constructor
    · rintro ⟨-, h⟩ PP -
      exact h PP.1 PP.2
    · intro h
      exact ⟨x.2, fun PP hP => h ⟨PP, hP⟩ (Set.mem_univ _)⟩
  have hsurj : Function.Surjective φ := by
    intro g
    let L' : LevDat D.host.E ℂ V.rank := Lev.datW V.rank (Pg ∪ Q) (LevelP.triv (Pg ∪ Q) V.rank ℂ) Lev.Frm.B
    have hlift : Lev.LiftsExist V β L' :=
      GlobalTheory.ParahoricLift.liftsExist V β L' Λ N hN (fun PP hP PP' hP' => by
        rcases hP' with h | h
        · exact hnc PP hP PP' h
        · exact absurd h (Finset.notMem_empty _)) (Finset.disjoint_empty_right _)
    let g0 : G0 L'.Pg L'.r := fun PP => if h : PP.1 ∈ Q then g ⟨PP.1, h⟩ else 1
    obtain ⟨κ, hκ⟩ := hlift g0
    have hκ1 : Lev.finE V κ ∈ parLev D.sp.cm V.gram β L' := hκ.2.1
    have hκ2 : rTup β L' (Lev.finE V κ) = g0 := hκ.2.2
    have hred : ∀ PP (h : PP ∈ Pg ∪ Q), redFn β PP (Lev.finE V κ) = g0 ⟨PP, h⟩ := by
      intro PP h
      exact (GlobalTheory.TwistIndex.restrictedBlock_self_apply _).symm.trans (congrFun hκ2 ⟨PP, h⟩)
    have hPg : ∀ PP ∈ Pg, redFn β PP (Lev.finE V κ) = 1 := by
      intro PP hP
      rw [hred PP (Finset.mem_union_left _ hP)]
      have hq : PP ∉ Q := Finset.disjoint_left.1 hd hP
      show (if h : PP ∈ Q then g ⟨PP, h⟩ else (1 : GL (Fin V.rank) (kP PP))) = 1
      exact dif_neg hq
    have hSt' := parLev_St hκ1
    have hxbig : Lev.finE V κ ∈
        lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) := by
      refine ⟨⟨⟨⟨parLev_UA hκ1, hSt'⟩, ?_⟩, ?_⟩, ?_⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
          mem_parah.2 ⟨hSt', by rw [hPg PP hP]; exact Subgroup.one_mem _⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
      · show rTup β (Lev.datY V.rank r t j hr Pg ∅ (LevelP.triv _ _ _) χ ξ' Lev.Frm.B) (Lev.finE V κ) ∈
          (⊥ : Subgroup (G0 Pg r))
        refine Subgroup.mem_bot.2 (funext fun PP => ?_)
        show upperLeftBlock hr (redFn β PP.1 (Lev.finE V κ)) = 1
        rw [hPg PP.1 PP.2]
        exact blockDiagonalExtendByOnePrimeField_one _ _
    refine ⟨⟨_, hxbig⟩, funext fun PP => ?_⟩
    rw [hφ, hred PP.1 (Finset.mem_union_right _ PP.2)]
    show (if h : PP.1 ∈ Q then g ⟨PP.1, h⟩ else 1) = g PP
    rw [dif_pos PP.2]
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, GlobalTheory.TwistIndex.index_pi_univ]
  exact Finset.prod_coe_sort Q fun PP => (blockTri (blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))).index

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem Q_base (h : L.Is μ₀) : L.Q μ₀ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h1 := (h.Q_ram μ₀ PP).2 (Or.inl hPP)
  rw [h.xi_base] at h1
  exact h1 fun _ _ => rfl

open Classical in

theorem not_conj (h : L.Is μ₀) (t : T) : ∀ P ∈ L.Pg ∪ L.Q t, ∀ P' ∈ L.Pg ∪ L.Q t, ¬ Lev.IsConjPl P P' := by
  intro P hP P' hP' hc
  rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'
  · obtain ⟨k, hk⟩ := (h.Pg P).1 hP
    obtain ⟨k', hk'⟩ := (h.Pg P').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl L.C.P hk hk' hc
  · obtain ⟨k, hk⟩ := (h.Pg P).1 hP
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes P' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))
  · obtain ⟨k, hk⟩ := (h.Pg P').1 hP'
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP
    exact GlobalTheory.LevelRamif.not_two_primes P' hq (D.host.g_prime k) (hne k) (GlobalTheory.LevelRamif.natCast_mem_conj hc hm)
      (GlobalTheory.LevelRamif.typePrime_mem hk)
  · exact (h.Q_pl t P hP).2 P' hP' hc

theorem relIndex_levCol (h : L.Is μ₀) (t : T) {j : ℕ} (hj : j + 1 < D.R.m) :
    levCol L t j ≤ levCol L μ₀ j ∧ levCol L μ₀ j ≤ UA D.sp.cm (columnBlock L (j + 1)).sp.gram ∧
      (levCol L t j).relIndex (levCol L μ₀ j) =
        ∏ PP ∈ L.Q t, (blockTri (blk2 D.R.r) : Subgroup (GL (Fin (Yc D (j + 1)).rank) (kP PP))).index := by
  obtain ⟨c, hc⟩ := h.βY (j + 1) hj
  have H := relIndex_lev (Yc D (j + 1)) (L.βY (j + 1)) _ _ hc (t := D.R.t) (j := j + 1) (r_le_Y (j + 1)) L.Pg (L.Q t)
    (not_conj h t) (GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ h t ⟨j + 1, hj⟩).1 L.chi (L.xiR t) (L.xiR μ₀)
  have e0 : L.datYt μ₀ (j + 1) L.triv = Lev.datY _ D.R.r D.R.t (j + 1) (r_le_Y (j + 1)) L.Pg ∅ (LevelP.triv _ _ _) L.chi
      (L.xiR μ₀) Lev.Frm.B := by
    rw [LevCh.datYt, Q_base h]
  rw [← e0] at H
  have key : ∀ (Y : LSp D) (V : HSp D) Λ (K K₀ : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D)))
      (K' K₀' : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (n : ℕ), Y = ⟨V, Λ⟩ → HEq K K' → HEq K₀ K₀' →
      K' ≤ K₀' → K₀' ≤ UA D.sp.cm V.gram → K'.relIndex K₀' = n → K ≤ K₀ ∧ K₀ ≤ UA D.sp.cm Y.sp.gram ∧ K.relIndex K₀ = n := by
    rintro _ V Λ K K₀ K' K₀' n rfl e e' a b c
    obtain rfl := eq_of_heq e
    obtain rfl := eq_of_heq e'
    exact ⟨a, b, c⟩
  exact key _ _ _ _ _ _ _ _ (colY_lt L hj) (levCol_lt L t hj) (levCol_lt L μ₀ hj) H.1 lev_le_UA H.2

theorem nu_scale {M M₀ : Vol G} {X : Node} {K₁ K₀ : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))}
    (h₁ : M.IsAt X K₁) (h₀ : M₀.IsAt X K₀) (hle : K₁ ≤ K₀) (hU : K₀ ≤ UA D.sp.cm (G.V X).gram) (hne : K₁.relIndex K₀ ≠ 0)
    (ho : IsOpen ((K₁.comap (Lev.finE (G.V X)) : Subgroup (GA D (G.V X))) : Set (GA D (G.V X)))) :
    M.ν X = (K₁.relIndex K₀ : ℝ≥0∞) • M₀.ν X := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V X)
  unfold GlobalTheory.FunObj.Vol.IsAt at h₁ h₀
  split_ifs at h₁ h₀
  · exact GlobalTheory.ChainTw.VolScale.scale _ _ (fun _ _ hm => hm.1) _ _ _ _ hle hU hne ho.measurableSet h₁.1 h₀.1
  · exact GlobalTheory.ChainTw.VolScale.scale _ _ (fun _ _ hm => hm.1) _ _ _ _ hle hU hne ho.measurableSet h₁.1 h₀.1

theorem levVol_of_KO {t : T} {i j : Fin D.R.m} {w : Pl D.host.E} (h : givenLevel G t w (i, j) = KO (Kw w) _) :
    levVol G t i j w = 1 := by
  have := vol_mul_relIndex (KO (Kw w) (Fin ((locGrid G t w).rank (i, j)))) GlobalTheory.SplitFlip.isOpen_KO le_rfl
  rw [Subgroup.relIndex_self, Nat.cast_one, mul_one] at this
  rw [levVol, h]
  exact this

theorem levVol_ne_zero (hL : L.Is μ₀) {t : T} (i j : Fin D.R.m) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    levVol G t i j w ≠ 0 := by
  have h := GivenAdm.givenLevel_open (G := G) hL hw ((i : ℕ), (j : ℕ))
  exact left_ne_zero_of_mul_eq_one (vol_mul_relIndex _ h.1 h.2)

theorem givenLevel_base (hL : L.Is μ₀) (j : ℕ) {w : Pl D.host.E} (hw : w ∉ L.Pg) :
    givenLevel G μ₀ w (0, j + 1) = KO (Kw w) _ := by
  ext g
  refine (GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description G μ₀ w hw (j + 1) g).trans ?_
  simp [Q_base hL]

theorem levVol_base (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {w : Pl D.host.E} (hw : w ∈ L.Q t) (hw' : w ∉ G.pl.W0) :
    levVol G μ₀ i j w = 1 := by
  refine levVol_of_KO ?_
  have hP : w ∉ L.Pg := Finset.disjoint_right.1 (GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t i).1 hw
  obtain ⟨i, hi⟩ := i
  obtain ⟨_ | j, hj⟩ := j
  · ext g
    show g ∈ glLatCong (unifAt w ^ cosExp G w) (GlobalTheory.SplitFlip.stdLat (Kw w) _) ↔ _
    rw [(depthAt_of_notMem G hw').1, pow_zero, GivenAdm.mem_glLatCong]
    refine and_iff_left_of_imp fun hg a b => ?_
    have := ((GlobalTheory.SplitFlip.mem_KO_iff g).1 hg).1 a b
    simp only [Units.val_one, map_one, Matrix.sub_apply]
    refine Valuation.map_sub_le _ this ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  · rcases i with _ | i
    · exact givenLevel_base hL j hP
    · rfl

theorem levVol_col (hL : L.Is μ₀) (t : T) {j : ℕ} (hi : 0 < D.R.m) (hj : j + 1 < D.R.m) {w : Pl D.host.E} (hw : w ∉ L.Q t) :
    levVol G t ⟨0, hi⟩ ⟨j + 1, hj⟩ w = levVol G μ₀ ⟨0, hi⟩ ⟨j + 1, hj⟩ w := by
  have e : stepGroup L t w (j + 1) = stepGroup L μ₀ w (j + 1) := by
    simp [stepGroup, hw, Q_base hL]
  have a : ∀ t' : T, levVol G t' ⟨0, hi⟩ ⟨j + 1, hj⟩ w =
      (haarVol (KO (Kw w) (Fin ((locGrid G μ₀ w).rank (0, j + 1))))).real
        (((stepGroup L t' w (j + 1)).map (GlobalTheory.StepData.reGL (ixFin G μ₀ w (j + 1))).toMonoidHom).map invT : Subgroup _) :=
    fun _ => rfl
  rw [a, a, e]

theorem exists_factors (hL : L.Is μ₀) (i j : Fin D.R.m) (t : T) {M M₀ : Vol G} (hM : M.Is t) (hM₀ : M₀.Is μ₀) :
    ∃ n : Pl D.host.E → ℕ, M.ν (.grid i j) = ((∏ w ∈ L.Q t, n w : ℕ) : ℝ≥0∞) • M₀.ν (.grid i j) ∧
      (∀ w ∈ L.Q t, levVol G t i j w * n w = levVol G μ₀ i j w) ∧ ∀ w ∉ L.Q t, levVol G t i j w = levVol G μ₀ i j w := by
  have hX : (Node.grid i j).InRange D.R.m := ⟨i.2.le, j.2.le⟩
  have easy : levJ G t (.grid i j) = levJ G μ₀ (.grid i j) → (∀ w, levVol G t i j w = levVol G μ₀ i j w) →
      ∃ n : Pl D.host.E → ℕ, M.ν (.grid i j) = ((∏ w ∈ L.Q t, n w : ℕ) : ℝ≥0∞) • M₀.ν (.grid i j) ∧
      (∀ w ∈ L.Q t, levVol G t i j w * n w = levVol G μ₀ i j w) ∧ ∀ w ∉ L.Q t, levVol G t i j w = levVol G μ₀ i j w := by
    intro e h
    refine ⟨fun _ => 1, ?_, fun w _ => by rw [h, Nat.cast_one, mul_one], fun w _ => h w⟩
    rw [Finset.prod_const_one, Nat.cast_one, one_smul]
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M₀ _ _ (hM.vtx _ hX) (e ▸ hM₀.vtx _ hX)
  obtain ⟨i, hi⟩ := i
  obtain ⟨_ | j, hj⟩ := j
  · exact easy ((levJ_row G t i).trans (levJ_row G μ₀ i).symm) fun _ => rfl
  rcases i with _ | i
  swap
  · exact easy rfl fun _ => rfl
  obtain ⟨h1, h2, h3⟩ := relIndex_levCol hL t hj
  have hne : (levCol L t j).relIndex (levCol L μ₀ j) ≠ 0 := by
    rw [h3]
    exact Finset.prod_ne_zero_iff.2 fun w _ => Subgroup.index_ne_zero_of_finite
  refine ⟨fun PP => (blockTri (blk2 D.R.r) : Subgroup (GL (Fin (Yc D (j + 1)).rank) (kP PP))).index, ?_,
    fun w hw => ?_, fun w hw => ?_⟩
  · rw [← h3]
    exact nu_scale (X := .grid 0 (j + 1)) (hM.vtx _ hX) (hM₀.vtx _ hX) h1 h2 hne (levJ_open_compact G hL t hX).1
  · classical
    have hP : w ∉ L.Pg := Finset.disjoint_right.1 (GlobalTheory.LevelRamif.ramif_at_levels D T L μ₀ hL t ⟨0, hi⟩).1 hw
    have ho := GivenAdm.givenLevel_open (G := G) hL (t := t) (w := w) (by unfold locPl; simp [hw]) (0, j + 1)
    have hv := vol_mul_relIndex _ ho.1 ho.2
    rw [relIndex_parahoric D.R.r (givenLevel G t w (0, j + 1)) (fun g => (GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description G t w hP (j + 1) g).trans (by simp [hw])),
      index_residue w (s := (j + 1) * D.R.t) (n' := (Yc D (j + 1)).rank)
        (by change D.R.r + (j + 1) * D.R.t + 0 * sLen D = _; rw [zero_mul, add_zero])
        ((D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [min_eq_left hj.le]; rfl))] at hv
    rw [levVol_of_KO (t := μ₀) (givenLevel_base hL j hP)]
    exact hv
  · exact levVol_col hL t hi hj hw

theorem measure_mul_levVol : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → (∀ t, SquareStanding G t) → ∀ (i j : Fin D.R.m) (m : Measure (GA D (spW₁ G i j))), m.IsHaarMeasure →
      ∃ c : ℝ, c ≠ 0 ∧ ∀ (t : T) (M : Vol G), M.Is t → ∀ s : NNReal, M.ν (.grid i j) = s • m →
        (s : ℝ) * ∏ w ∈ locPl G t, levVol G t i j w = c := by
  intro D T L sc G μ₀ hL _ i j m hm
  classical
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (spW₁ G i j)
  obtain ⟨M₀, hM₀⟩ := exists_vol G hL μ₀
  have hX : (Node.grid i j).InRange D.R.m := ⟨i.2.le, j.2.le⟩
  haveI := (hM₀.vtx _ hX).haar_fund.1
  have e₀ := Measure.isMulLeftInvariant_eq_smul (M₀.ν (.grid i j)) m
  have p₀ := Measure.haarScalarFactor_pos_of_isHaarMeasure (M₀.ν (.grid i j)) m
  set s₀ := Measure.haarScalarFactor (M₀.ν (.grid i j)) m
  refine ⟨s₀ * ∏ w ∈ locPl G μ₀, levVol G μ₀ i j w, mul_ne_zero (by exact_mod_cast p₀.ne')
    (Finset.prod_ne_zero_iff.2 fun w hw => levVol_ne_zero hL i j hw), fun t M hM s hs => ?_⟩
  obtain ⟨n, h1, h2, h3⟩ := exists_factors hL i j t hM hM₀
  have hsn : (s : ℝ) = (∏ w ∈ L.Q t, n w : ℕ) * (s₀ : ℝ) := by
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : GA D (spW₁ G i j))
    have h0 : m C ≠ 0 := (Measure.measure_pos_of_mem_nhds m hC1).ne'
    have h := congrArg (fun μ : Measure (GA D (spW₁ G i j)) => μ C) (hs.symm.trans h1)
    rw [e₀] at h
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ← mul_assoc] at h
    have h' := congrArg ENNReal.toReal ((ENNReal.mul_left_inj h0 hC.measure_lt_top.ne).1 h)
    simpa using h'
  have hsub : locPl G μ₀ ⊆ locPl G t := by
    unfold locPl
    rw [Q_base hL]
    simp
  have hQ : L.Q t ⊆ locPl G t := by
    unfold locPl
    simp
  have e1 : ∏ w ∈ locPl G μ₀, levVol G μ₀ i j w = ∏ w ∈ locPl G t, levVol G μ₀ i j w :=
    Finset.prod_subset hsub fun w hw hw' => by
      have a : w ∉ G.pl.W0 := fun h => hw' (by unfold locPl; simp [h])
      exact levVol_base hL t i j (by unfold locPl at hw; simpa [a] using hw) a
  rw [hsn, e1, ← Finset.prod_sdiff hQ, ← Finset.prod_sdiff hQ (f := levVol G μ₀ i j),
    ← Finset.prod_congr rfl h2, Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun w hw => h3 w (Finset.mem_sdiff.1 hw).2, Nat.cast_prod]
  ring

end GlobalTheory.TopFlip.MeasLevel

end
end

section
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

set_option maxHeartbeats 1600000 in

private theorem tuple_match' (hP : GlobalTheory.FunPr.Hypotheses₂) (hTL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hL : L.Is μ₀) (W : G.Weil) (i j : Fin D.R.m)
    {A : Fr (spW G i j)} {A₁ : Fr (spW₁ G i j)} {AV : Fr (spV G i j)} {AV₁ : Fr (spV₁ G i j)} (hA : IsGridFr W _ A)
    (hA₁ : IsGridFr W _ A₁) (hV : IsGridFr W _ AV) (hV₁ : IsGridFr W _ AV₁) (t : T) (B : Frames G) (ρ : RealMatch W) (M : Vol G)
    (hst : SquareStanding G t) (hM : M.Is t) {ωA ωB}
    (hωA : GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA)
    (hωB : GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB) :
    ∃ Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωA ωB Pi rf rl p p' ∧
      ∀ ε, IsIdemSum ε (locPl G t) → ∀ Ξ Ψ (u : Pl D.host.E → ℂ) F F',
        (∀ w ∈ locPl G t, Ξ w ∈ GlobalTheory.WeilM.SB _ ∧ Ψ w ∈ GlobalTheory.WeilM.SB _ ∧ zetaA G t i j w (Ξ w) = u w • zetaB G t i j w (Ψ w)) →
        IsLinA B t i j ρ ε Ξ F → IsLinB B t i j ρ ε Ψ F' →
        ∀ n Φ (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)),
        (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip B t ρ i j n Φ τ τ' →
        IsFinF W.ψ W.θ true A (frSum AV AV₁) F ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) F' ∧
        IsFinF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') ∧
        ∀ P P' (g : ℂ), p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) F' P') ≠ 0 →
          p (fockF W.ψ W.θ true A (frSum AV AV₁) F P) = g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) F' P') →
          ((∏ w ∈ locPl G t, u w) * ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ)) •
              p (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) =
            g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') P') := by
  have hT := (GlobalTheory.SquareDict.dict hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁).1 hst M hM
  obtain ⟨e, Bs, Γ, X, om₀, om₀', h, hT₀, hti⟩ := exists_tiedBoth hL W t i j hst M hM
  have hR : GlobalTheory.TripleRead.IsReading W.ψ A A₁ (frSum AV AV₁) _ _ (e.symm.trans finSumFinEquiv) Bs Γ X :=
    ⟨h.ψ, h.JW, h.JW₁, by
      rw [h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, ← GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_transpose, ← GlobalTheory.SquareIdent.blkMat_submatrix, GlobalTheory.Doubling.gram_hsum]
      rfl, fun w => by
      obtain ⟨τ, a, b, c, d⟩ := h.cart w
      refine ⟨τ, a, b.trans (hA τ).2.symm, c.trans (congrArg Neg.neg (hA₁ τ).2.symm), d.trans ?_⟩
      rw [GlobalTheory.SquareAlg.cart_frSum, (hV τ).2, (hV₁ τ).2, ← GlobalTheory.SquareIdent.blkMat_submatrix], h.α, h.β⟩
  obtain ⟨om, om', R, Rf, hm, rf, rl, p, p', hM', HA, HB⟩ :=
    match_tens hP.howeDualityReal hP hTL W.θ_is A A₁ _ hT hωA hωB hR hT₀
  have hT' := hm.triple
  have H := fun (w : Pl D.host.E) (hw : w ∈ locPl G t) => local_charts hL W B t i j M hst h hm hti hw
  choose! ιA ι ιB ι' l hl h1 h2 h3 h4 h5 h6 h7 using H
  obtain ⟨f, -, f2, f3⟩ := GlobalTheory.T.exists_gaussianVacuum_product_unitVacua hL W ρ t i j M hst e Bs Γ X om om' h hT' hti.1
  obtain ⟨f', -, g2, g3⟩ := GlobalTheory.T.unitVacua_product_eq_gaussianDatum_smallModel hL W ρ t i j M hst e Bs Γ X om om' h hT' hti
  obtain ⟨hs, a⟩ := mixglobA hL W B ρ t i j M hst e Bs Γ X om om' h hT' hti.1 f f3 ι h3
  obtain ⟨hs', b⟩ := mixglobB hL W B ρ t i j M hst e Bs Γ X om om' h hT' hti f' g3 ι' h4
  have vA : ∏ w ∈ locPl G t, ιA w (Γ.M.vac _) 0 = ∏ w ∈ locPl G t, ι w (Γ.M.vac _) 0 := Finset.prod_congr rfl fun w hw => by
    have k := GlobalTheory.T.mixedModel_vacuum_eq_integralMatrix_indicator hL W B t i j M hst e Bs Γ X om om' h hT' hti.1 w hw _ (h3 w hw)
    have k2 := fourierSum_ind (A := Fin ((locGrid G t w).rank (i + 1, j + 1))) (psiAt W w)⁻¹ (isUnif_unifAt w)
      (Assignment.one.block (Fin ((locGrid G t w).rank (i, j + 1))) (Fin ((locGrid G t w).rank (i + 1, j))))ᶜ (ι w (Γ.M.vac _) 0)
    rw [← k] at k2
    rw [h5 w hw _ (hT'.geo.hM.vac _).1 0 k2.1, k2.2]
  have vB : ∏ w ∈ locPl G t, ιB w (Γ.M'.vac _) 0 = ∏ w ∈ locPl G t, ι' w (Γ.M'.vac _) 0 := Finset.prod_congr rfl fun w hw => by
    have k := GlobalTheory.T.mixedModel_vacuum_eq_smul_integralMatrix_indicator hL W B t i j M hst e Bs Γ X om om' h hT' hti w hw _ (h4 w hw)
    have k2 := fourierSum_ind (A := Fin ((locGrid G t w).rank (i, j))) (psiAt W w) (isUnif_unifAt w)
      (Assignment.one.block (Fin ((locGrid G t w).rank (i, j + 1))) (Fin ((locGrid G t w).rank (i + 1, j)))) (ι' w (Γ.M'.vac _) 0)
    rw [← k] at k2
    rw [h6 w hw _ (hT'.geo.hM'.vac _).1 0 k2.1, k2.2]
  have la := GlobalTheory.T.negW_local_functions_theta_pure_tensor hL W B t i j M hst e Bs Γ X om om' h hT' hti.1 ρ f
    (datumA_vac ρ i j t ▸ GlobalTheory.SquareIdent.isDatum_of_isDatumA f3) ιA h1
  have lb := GlobalTheory.TopFlip.LinSmall.isDatum_linB hL W B t i j M hst e Bs Γ X om om' h hT' hti ρ f'
    (datumB_vac ρ i j t ▸ GlobalTheory.SquareIdent.isDatum_of_isDatumB g3) ιB h2
  rw [vA] at la
  rw [vB] at lb
  refine ⟨_, rf, rl, p, p', hM', fun ε hε Ξ Ψ u F F' hΞ hF hF' n Φ τ τ' hn ⟨ε', hε', c, d⟩ => ?_⟩
  have hf : ∀ w ∈ locPl G t, IsNatDatum (unifAt w) (n w) (flipAt W t i j w (n w) (Φ w)) := fun w hw =>
    LocTensor.isNatDatum_flipAt hL W i j hw (notMem_of_standing hst hw) (hn w hw).1 (hn w hw).2
  have hinj : ∀ w ∈ locPl G t, ∀ w' ∈ locPl G t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w = w' :=
    fun w hw w' hw' e => Good.under_injOn hL G t hw hw' e
  obtain ⟨φ, p1, p2⟩ := exists_finPart hT'.geo.hM hti.1.2.2.1 hinj (fun w φ => ι w φ = flipAt W t i j w (n w) (Φ w))
    fun w hw => (h3 w hw).1.2.2 (mem_SB_of_isNatDatum (hf w hw))
  obtain ⟨φ', q1, q2⟩ := exists_finPart hT'.geo.hM' hti.1.2.2.1 hinj (fun w φ => ι' w φ = Φ w)
    fun w hw => (h4 w hw).1.2.2 (mem_SB_of_isNatDatum (hn w hw).2)
  obtain ⟨χ, r1, r2⟩ := exists_finPart hT'.geo.hM hti.1.2.2.1 hinj (fun w φ => ιA w φ = Ξ w)
    fun w hw => (h1 w hw).1.2.2 (hΞ w hw).1
  obtain ⟨χ', s1, s2⟩ := exists_finPart hT'.geo.hM' hti.1.2.2.1 hinj (fun w φ => ιB w φ = Ψ w)
    fun w hw => (h2 w hw).1.2.2 (hΞ w hw).2.1
  have dA := GlobalTheory.SquareIdent.isDatum_of_isDatumA (a ε' hε' n _ τ hf d φ p1 p2)
  have dB := GlobalTheory.SquareIdent.isDatum_of_isDatumB (b ε' hε' n _ τ' (fun w hw => (hn w hw).2) c φ' q1 q2)
  have dF := la ε hε Ξ F hF χ r1 r2
  have dF' := lb ε hε Ψ F' hF' χ' s1 s2
  have gA := isGauss_smul f2 hs
  have gB := isGauss_smul g2 hs'
  have y₀ := pureT_loc hL hm hti.1 r1 s1 (c := fun w => l w * u w) fun w hw =>
    h7 w hw _ (r1.1 _) _ (s1.1 _) _ (by rw [r2 w hw, s2 w hw]; exact (hΞ w hw).2.2)
  have y₁ := pureT_loc hL hm hti.1 p1 q1 (c := fun w => l w * ((levVol G t i j w : ℝ) : ℂ)⁻¹) fun w hw =>
    h7 w hw _ (p1.1 _) _ (q1.1 _) _ (by
      rw [h5 w hw _ (p1.1 _) (n w) (by rw [p2 w hw]; exact hf w hw), h6 w hw _ (q1.1 _) (n w) (by rw [q2 w hw]; exact (hn w hw).2),
        p2 w hw, q2 w hw]
      exact (zeta_flip hL W i j hst hw).2 _ _ (hn w hw).1 (hn w hw).2)
  obtain ⟨_, k1⟩ := HA _ gA 0
  obtain ⟨_, k2⟩ := HB _ gB 0
  refine ⟨(k1 _ r1 _ dF).1, (k2 _ s1 _ dF').1, (k1 _ p1 _ dA).1, (k2 _ q1 _ dB).1, fun P P' g hne hg => ?_⟩
  obtain ⟨x, hx⟩ := HA _ gA P
  obtain ⟨y, hy⟩ := HB _ gB P'
  rw [(hy _ s1 _ dF').2] at hne hg
  rw [(hx _ r1 _ dF).2, y₀] at hg
  rw [(hx _ p1 _ dA).2, (hy _ q1 _ dB).2, y₁]
  generalize (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (χ' v)) = z₀ at hne hg
  generalize (GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) fun v => Rf.p' v (φ' v)) = z
  have hz : z₀ ≠ 0 := fun h0 => hne (by rw [h0, TensorProduct.tmul_zero])
  obtain ⟨lz, hlz⟩ := Module.Projective.exists_dual_eq_one ℂ hz
  have e1 : (∏ w ∈ locPl G t, l w * u w) • x = g • y := by
    have := congrArg (TensorProduct.rid ℂ R.Pi ∘ LinearMap.lTensor R.Pi lz) hg
    simpa [hlz] using this
  have hV : ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun w hw => (zeta_flip hL W i j hst hw).1)
  have e2 : (∏ w ∈ locPl G t, u w) * ((∏ w ∈ locPl G t, levVol G t i j w : ℝ) : ℂ) *
      ∏ w ∈ locPl G t, l w * ((levVol G t i j w : ℝ) : ℂ)⁻¹ = ∏ w ∈ locPl G t, l w * u w := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Complex.ofReal_prod]
    field_simp
  change _ • (x ⊗ₜ[ℂ] (_ • z) : GlobalTheory.TripleAssembly.PiT R Γ Rf) = g • (y ⊗ₜ[ℂ] z : GlobalTheory.TripleAssembly.PiT R Γ Rf)
  rw [TensorProduct.tmul_smul, smul_smul, e2, TensorProduct.smul_tmul', e1, TensorProduct.smul_tmul']

end GlobalTheory.TopFlip

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

private theorem awayIm_inv {D : D7} {m : ℕ} {z : ℂ} (h : GlobalTheory.KappaArith.AwayIm D m z) : GlobalTheory.KappaArith.AwayIm D m z⁻¹ := by
  obtain ⟨ζ, ⟨a, k, k', ⟨b, hb⟩, ha⟩, rfl⟩ := h
  refine ⟨ζ⁻¹, ?_, map_inv₀ _ _⟩
  by_cases hm : m = 0
  · subst hm
    exact ⟨0, 1, 1, by simp, by simp⟩
  have hm' : (m : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hb' : (m : D.what₂.LL) ^ k' = (a : D.what₂.LL) * (b : D.what₂.LL) := by exact_mod_cast congrArg (fun x : 𝓞 D.what₂.LL => (x : D.what₂.LL)) hb
  have hζ : ζ ≠ 0 := fun h0 => pow_ne_zero k' hm' (by rw [hb', ← ha, h0, zero_mul, zero_mul])
  refine ⟨b * (m : 𝓞 D.what₂.LL) ^ k, k', k' + k, ⟨a, by rw [pow_add, hb]; ring⟩, ?_⟩
  have e : ((b * (m : 𝓞 D.what₂.LL) ^ k : 𝓞 D.what₂.LL) : D.what₂.LL) = (b : D.what₂.LL) * (m : D.what₂.LL) ^ k := by push_cast; rfl
  rw [e, hb', ← ha]
  field_simp

private theorem move_rel {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {W W₁ X : HSp D} {A : Fr W}
    {A₁ : Fr W₁} {B : Fr X} {α β : (AE D)ˣ →* Circle} {ωA ωB Pi rf rl p p'} (hm : IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p')
    {h : GA D X} (hh : h ∈ GfC X) {f f'} (hf : IsFinF ψ θ true A B f) (hf' : IsFinF ψ θ false A₁ B f') {a b : ℂ} (hb : b ≠ 0)
    {P P'} {g : ℂ} (hne : p' (fockF ψ θ false A₁ B f' P') ≠ 0)
    (hg : p (fockF ψ θ true A B f P) = g • p' (fockF ψ θ false A₁ B f' P')) :
    p' (fockF ψ θ false A₁ B (b⁻¹ • ωB (1, h) f') P') ≠ 0 ∧
      p (fockF ψ θ true A B (a • ωA (1, h) f) P) = (a * g * b) • p' (fockF ψ θ false A₁ B (b⁻¹ • ωB (1, h) f') P') := by
  have mA : fockF ψ θ true A B f P ∈ algF ψ θ true A B := Submodule.subset_span ⟨_, _, hf, rfl⟩
  have mB : fockF ψ θ false A₁ B f' P' ∈ algF ψ θ false A₁ B := Submodule.subset_span ⟨_, _, hf', rfl⟩
  rw [om_fockF hθ A B hm.weilA hh hf, om_fockF hθ A₁ B hm.weilB hh hf', map_smul, map_smul, hm.mapA.eqf h hh _ mA, hg, map_smul,
    hm.mapB.eqf h hh _ mB]
  refine ⟨smul_ne_zero (inv_ne_zero hb) fun h0 => hne ?_, ?_⟩
  · have e := hm.mapB.eqf h⁻¹ (inv_mem hh) _ (hm.mapB.stabX.1 h hh _ mB)
    rw [hm.mapB.eqf h hh _ mB, h0, map_zero, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, one_mul,
      ← Prod.one_eq_mk, map_one, Module.End.one_apply] at e
    exact e
  · rw [smul_smul, smul_smul, mul_assoc, mul_inv_cancel₀ hb, mul_one]

end GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_grid_stage_polynomial_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (M : Vol G), M.Is t → ∀ s s' : NNReal, M.ν (.grid (i + 1) (j + 1)) = s • X.m → M.ν (.grid i j) = s' • X.m' →
      ∀ Pi rf rl p p', IsMatch W.ψ W.θ A A₁ (frSum AV AV₁) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (X.ω t) (X.ω' t) Pi rf rl p p' →
      ∀ n Φ (τ : TotT G (routeBig t i j)) (τ' : TotT G (routeSmall t i j)), (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) → HasFlip S.B t ρ i j n Φ τ τ' →
      ∀ P P' (g : ℂ), p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) P') ≠ 0 →
        p (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) P) = g • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) P') →
        ((s : ℝ) : ℂ) • p (fockF W.ψ W.θ true A (frSum AV AV₁) (datumA W τ) P) =
          (κ t * ((s' : ℝ) : ℂ) * g) • p' (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (datumB W τ') P') := by
  intro hP hK hM
  obtain ⟨F1, H1⟩ := GlobalTheory.T.grid_frames_doubling_polynomial_exists hP
  obtain ⟨F2, H2⟩ := GlobalTheory.T.square_tower_frame_compat hP hK hM
  refine ⟨max F1 F2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, H1⟩ := H1 ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, H2⟩ := H2 ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  replace H1 := H1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G
  replace H2 := H2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G
  have hst : ∀ t, SquareStanding G t := fun t => GlobalTheory.ThetaRegularizationComparison.standing hR hR.size.2.1.eleven_le hL G t
  intro W S hψ hN ρ i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  obtain ⟨σ, σ', hσ⟩ := H1 W i j X hTG hSC A A₁ AV AV₁ hA hA₁ hV hV₁
  replace H2 := H2 W i j _ _ _ _ _ X hSC A A₁ (frSum AV AV₁)
  have hIs := hSC.2.2.2.2.2.2.2
  have hrk : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.eps G i j = rankV D i j % 2 := congrArg (· % 2) (Nat.add_right_cancel hSC.2.2.2.1)
  have eα : ∀ t, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j = Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) := fun t => by
    rw [← hrk]; rfl
  have eβ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2) := by
    rw [← hrk]; rfl
  have hI : X.Is W.ψ W.θ (fun t => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (fun _ => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (fun t => nuH G t i j)
      (locPl G) := by
    simp only [eα, eβ]
    exact hIs
  obtain ⟨h, hh, cA, cB, y, hcA, hcB, hmv⟩ := GlobalTheory.TopFlip.exists_move hL hst S.B ρ hTG hI hV hV₁
  obtain ⟨x, hx⟩ := GlobalTheory.TopFlip.zeta_std hL W S.B X hst (hTG.1 ▸ hI.rigA.2.1) (hTG.2.1 ▸ hI.rigA'.2.1)
    (by have := hI.rigW.2.1; rwa [hTG.2.2.1] at this)
  obtain ⟨s₀, hs₀, hs⟩ := GlobalTheory.TopFlip.MeasW.exists_ratio (G := G) hL i j X.m hI.meas.1
  obtain ⟨c₁, hc₁, hc⟩ := GlobalTheory.TopFlip.MeasLevel.measure_mul_levVol (G := G) hL hst i j X.m' hI.meas'.1
  set u : T → ℂ := fun t => ∏ w ∈ locPl G t, (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) with hu
  have hu0 : ∀ t, u t ≠ 0 := fun t => Finset.prod_ne_zero_iff.2 fun w _ => Units.ne_zero _
  have hξ0 : ∀ t, ((Lc.xi t y : Circle) : ℂ) ≠ 0 := fun t => Circle.coe_ne_zero _
  have hs₀' : ((s₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs₀
  have hc₁' : (c₁ : ℂ) ≠ 0 := by exact_mod_cast hc₁
  refine ⟨fun t => ((s₀ : ℝ) : ℂ) * cA⁻¹ * cB * (c₁ : ℂ)⁻¹ * ((Lc.xi t y : Circle) : ℂ) * (u t)⁻¹, fun t => ⟨?_, ?_⟩, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs₀' (inv_ne_zero hcA)) hcB) (inv_ne_zero hc₁')) (hξ0 t))
      (inv_ne_zero (hu0 t))
  · obtain ⟨z, hz, ez⟩ := GlobalTheory.TopFlipNu.nu_arith hL hN.chars i j x t fun w hw => (hx t w hw).1
    obtain ⟨ζ, h1, h2⟩ := ((GlobalTheory.XiAway.xi_awayIm hL t (hN.chars.xi t) (Qn G t) y).mul
      (GlobalTheory.TopFlip.awayIm_inv (GlobalTheory.XiAway.xi_awayIm hL μ₀ (hN.chars.xi μ₀) (Qn G t) y))).mul (GlobalTheory.TopFlip.awayIm_inv hz)
    refine ⟨ζ, h1, ?_⟩
    have e : u t = z * u μ₀ := ez
    have := hξ0 μ₀
    dsimp only
    rw [h2, e, mul_inv]
    field_simp
  intro t M hM' s s' es es' Pi rf rl p p' hm n Φ τ τ' hn hfl P P' g hne hg
  obtain ⟨Pi₀, rf₀, rl₀, p₀, p₀', hm₀, H⟩ := GlobalTheory.TopFlip.tuple_match' hP hM hL W i j hA hA₁ hV hV₁ t S.B ρ M (hst t) hM'
    (hI.weil t) (hI.weil' t)
  obtain ⟨f1, f2, f3, f4, H⟩ := H _ (hI.idem t) _ _ _ _ _ (fun w hw => (hx t w hw).2) (hmv t).1 (hmv t).2 n Φ τ τ' hn hfl
  obtain ⟨E, c, hc0, eA, eB⟩ := H2 t Pi₀ rf₀ rl₀ p₀ p₀' Pi rf rl p p' (by rw [← eα, ← eβ]; exact hm₀) (by rw [← eα, ← eβ]; exact hm)
  obtain ⟨k1, k2⟩ := GlobalTheory.TopFlip.move_rel W.θ_is hm hh (hσ t).1 (hσ t).2.1 (a := cA⁻¹) (mul_ne_zero hcB (hξ0 t)) hne hg
  rw [eB _ (Submodule.subset_span ⟨_, _, f2, rfl⟩)] at k1 k2
  rw [eA _ (Submodule.subset_span ⟨_, _, f1, rfl⟩)] at k2
  have k3 := H P P' (c⁻¹ * (cA⁻¹ * g * (cB * ((Lc.xi t y : Circle) : ℂ)))) (fun h0 => k1 (by rw [h0, map_zero]))
    (E.injective (by rw [map_smul, mul_smul, ← k2, smul_smul, inv_mul_cancel₀ hc0, one_smul]))
  rw [eA _ (Submodule.subset_span ⟨_, _, f3, rfl⟩), eB _ (Submodule.subset_span ⟨_, _, f4, rfl⟩)]
  have e1 : s = s₀ := hs t M hM' s es
  have e2 : ((s' : ℝ) : ℂ) * ((∏ w ∈ locPl G t, GlobalTheory.TopFlip.levVol G t i j w : ℝ) : ℂ) = c₁ := by exact_mod_cast hc t M hM' s' es'
  have k4 := congrArg E k3
  rw [map_smul, map_smul] at k4
  change (u t * _) • _ = _ at k4
  generalize ((∏ w ∈ locPl G t, GlobalTheory.TopFlip.levVol G t i j w : ℝ) : ℂ) = V at e2 k4
  have hV0 : V ≠ 0 := fun h0 => hc₁' (by rw [← e2, h0, mul_zero])
  have hs' : ((s' : ℝ) : ℂ) ≠ 0 := fun h0 => hc₁' (by rw [← e2, h0, zero_mul])
  have := hu0 t
  rw [(eq_inv_smul_iff₀ (mul_ne_zero this hV0)).2 k4, smul_smul, smul_smul, smul_smul, e1, ← e2]
  congr 1
  field_simp
end
