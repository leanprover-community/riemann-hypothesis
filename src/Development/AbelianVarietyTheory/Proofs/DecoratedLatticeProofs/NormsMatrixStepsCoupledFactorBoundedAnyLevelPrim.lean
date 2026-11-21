import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminingLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTenth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTwelfth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSixth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFifth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedDatumSmallTypePrimeAnyLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSeventh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEighth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BadPrimesSharp
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEleventh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantNinth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantThird

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.ChainClassNumbersS

theorem card_orbits_le_exp {D : D7} {N : NumDatum} {X : Fields} {s : Seam D X} {Pr : Primes X} (hH : HostTie N s Pr)
    (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) {δ : Code N} {CY : ℝ} (hS : SizeRowsS CY N δ) {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N.Nm)
    {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (hST : ST ⊆ Pr.vT u) (hSG : SG = Pr.vGs)
    {G' D' : Type} [Group G'] [MulAction G' D'] (p : D' → DecoSet X.E n ST SG) (hp : Function.Injective p)
    (h : ∀ (g : UF X.E n) (x : D'), ∃ g' : G', p (g' • x) = (g, (1 : GLG X.E n SG)) • p x) :
    (Nat.card (MulAction.orbitRel.Quotient G' D') : ℝ) ≤ Real.exp (55 * errUnit N (Pr.T u)) := by
  have hrdeq := hH.rd_eq
  obtain ⟨-, -, -, -, -, -, hX, -, -, hP, -, -, hg, -⟩ := hH
  obtain ⟨⟨s1, -⟩, s2, -, s4, -⟩ := hS
  obtain ⟨hfin, hcount⟩ := GlobalTheory.DecoClassCount.card_classes_le X hX.ok n ST SG
  have hle := GlobalTheory.ChainClassNumbers.card_orbits_le_principal p hp h
  have hk : 5 ≤ N.R.k := by have := N.R.m_add_three_le_k; have := N.R.two_le_m; omega
  have hf : X.f = N.R.f := by
    have h1 : X.f = Nat.card X.Tau := Nat.card_eq_fintype_card.symm
    rw [h1, ← Nat.card_congr pl, Nat.card_prod, Nat.card_eq_fintype_card (α := N.R.A), N.R.card_A]
    simp [Ranks.f, Ranks.n]
  have hE : Module.finrank ℚ X.E = 2 * N.R.f := by
    have h1 := Module.finrank_mul_finrank ℚ X.F X.E
    rw [hX.ok.rankE, ← hX.ok.card_Tau] at h1
    rw [← hf, mul_comm]
    exact h1.symm
  have hf1 : 1 ≤ N.R.f := hf ▸ hX.ok.f_pos
  have hfib := GlobalTheory.ColumnClassLog.fibre_bound_le hP u n hn SG hSG
  rw [hf, hg 0, hg 1] at hfib
  have hsub : ∏ P ∈ ST, Ideal.absNorm P.asIdeal ^ n ≤ ∏ P ∈ Pr.vT u, Ideal.absNorm P.asIdeal ^ n := by
    refine Finset.prod_le_prod_of_subset_of_one_le' hST fun P hP' _ => ?_
    rw [hP.vT_norm u P hP']
    exact Nat.one_le_pow _ _ (hP.T_prime u).pos
  have hfib' := (Nat.mul_le_mul_right _ hsub).trans hfib
  have hrd : |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd := by
    have e : X.E ≃ₐ[ℚ] D.host.E := s.iE.toRatAlgEquiv
    have h1 : D.host.rdE = N.rd := hrdeq.symm
    rw [discr_eq_discr_of_algEquiv X.E e, e.toLinearEquiv.finrank_eq]
    exact h1
  have hrd0 : 0 < N.rd := by
    rw [← hrd]
    exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero _)) _
  have hL : 1 ≤ N.sc.L := Real.one_le_rpow N.sc.one_lt_alt.le N.sc.eps_pos.le
  have hb : 1 ≤ Real.exp N.sc.L := Real.one_le_exp (by linarith)
  have hg0 : Real.exp N.sc.L ≤ N.g 0 := by
    refine le_trans ?_ (s2 0).1
    have hk' : (1 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 1 ≤ N.R.k)
    have h1 : Real.exp N.sc.L ≤ (N.R.k : ℝ) * Real.exp N.sc.L := by nlinarith
    exact h1.trans (le_self_pow₀ (hb.trans h1) (by norm_num))
  have hlog := GlobalTheory.ColumnClassLog.log_le_of_count (Nat.card (MulAction.orbitRel.Quotient G' D')) N.R.f n N.Nm (N.g 0) (N.g 1)
    (Pr.T u) N.rd N.sc.L hf1 hn hnN (hP.T_prime u).pos hrd0 hL s1 s4 hg0 (N.g_prime 1).pos (by
      refine ((Nat.cast_le.2 hle).trans hcount).trans ?_
      rw [hrd, hE, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [pow_two n]
      exact_mod_cast hfib')
  refine (Real.le_exp_log _).trans (Real.exp_le_exp.2 (hlog.trans ?_))
  have hG : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u) := by
    have : 1 ≤ N.g 0 * N.g 1 * Pr.T u :=
      Nat.mul_pos (Nat.mul_pos (N.g_prime 0).pos (N.g_prime 1).pos) (hP.T_prime u).pos
    exact Real.log_nonneg (by exact_mod_cast this)
  have hm : (1 : ℝ) ≤ (N.R.m : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ N.R.m := by exact_mod_cast (by have := N.R.two_le_m; omega : 1 ≤ N.R.m)
    exact one_le_pow₀ this
  unfold errUnit
  calc 55 * (N.R.f : ℝ) * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u)
      = 55 * (N.R.f * 1 * (N.Nm : ℝ) ^ 2 * Real.log ((N.g 0 : ℝ) * N.g 1 * Pr.T u)) := by ring
    _ ≤ _ := by gcongr

theorem classNumbers_leS : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ j ≤ N.R.m, ∀ b : I.β j, (Nat.card ((chF W sel mu I u j).mem b).Cl : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ (Nat.card (evGSD W Ch sel mu (rPsymF Ch) u).Cl : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) ∧ (topClassNumber Ch sel mu u : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨55, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp
  obtain ⟨hH, -, -, -, hmu, -, -, -, hS⟩ := hyp
  have hQ : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
    rw [hmu]
    exact twistPrimes_trivialTuple_empty sel Sg
  have hSG : rowSG Pr sel mu = Pr.vGs := by
    unfold rowSG uSG
    ext w
    classical
    rw [Finset.mem_union, hQ]
    simp
  have hk : 5 ≤ N.R.k := by have := N.R.m_add_three_le_k; have := N.R.two_le_m; omega
  have hm : 2 ≤ N.R.N N.R.m := by unfold Ranks.N; omega
  refine ⟨fun j hj b => ?_, ?_, ?_⟩
  · have hn : 1 ≤ N.R.N j := by unfold Ranks.N; omega
    have hnN : N.R.N j ≤ N.Nm := by unfold NumDatum.Nm Ranks.N; gcongr
    refine @card_orbits_le_exp D N X s Pr hH pl u δ CY hS _ hn hnN _ _ subset_rfl rfl (FrmG (I.levG j b) (I.levQ j b))
      (ChPt (R := N.R) (Pr := Pr) sel mu u j) _ (frmAct (I.levG j b) (I.levQ j b)) DecoF.deco ?_
      fun g x => ⟨(g, 1, 1), rfl⟩
    intro x y hxy
    refine Subtype.ext (Prod.ext hxy (funext fun P => ?_))
    exact absurd P.2 (Finset.eq_empty_iff_forall_notMem.1 hQ P.1)
  · exact @card_orbits_le_exp D N X s Pr hH pl u δ CY hS (N.R.N N.R.m - 1) (by omega) (Nat.sub_le _ _) ∅ _ (Finset.empty_subset _) hSG
      (FormG (rowTy Ch sel mu (rPsymF Ch)).inv) (RowPt Pr N.R sel mu) _ (formAct (rowTy Ch sel mu (rPsymF Ch)).inv) id
      Function.injective_id fun g x => ⟨(g, 1), rfl⟩
  · unfold topClassNumber
    exact card_orbits_le_exp (n := N.R.N N.R.m) hH pl u hS (le_trans (by norm_num) hm) le_rfl subset_rfl hSG id Function.injective_id
      fun g x => ⟨⟨(g, 1), Subgroup.mem_prod.2 ⟨Subgroup.mem_top _, one_mem _⟩⟩, rfl⟩

end GlobalTheory.ChainClassNumbersS

end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.CouplingCosetsS

theorem ncard_ybSet_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ n ≤ N.Nm, (((ybSet sel mu cst (Formalism.L2.Col.stdLat X.E n)).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u))) ∧ ∀ L : Submodule (𝓞 X.E) (Sp X.E n), Submodule.IsLattice X.E L → ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  refine ⟨2, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H n hn
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, hmu, -⟩ := H
  have hf : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [← GlobalTheory.IndefiniteRowSideFullHecke.WeightedNormSquareDivisors.card_eq_f N X pl.symm, ← Module.finrank_mul_finrank ℚ X.F X.E, hX.ok.rankE, ← hX.ok.card_Tau, mul_comm]
    rfl
  have key : ∀ L : Submodule (𝓞 X.E) (Sp X.E n), ((ybSet sel mu cst L).ncard : ℝ) ≤ Real.exp (2 * errUnit N (Pr.T u)) := by
    intro L
    have h1 := (GlobalTheory.CouplingCosets.finite_ncard_ybSet hPr sel mu hmu cst L).2
    rw [hf, hg 0, hg 1] at h1
    have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
    have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
    have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
    have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
    have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
    have he : 2 * N.R.f * n ≤ 2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) := by
      refine Nat.mul_le_mul_left _ (hn.trans ?_)
      have hm : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by have := N.R.two_le_m; omega)
      calc N.Nm ≤ N.Nm ^ 2 := Nat.le_self_pow two_ne_zero _
        _ ≤ N.R.m ^ 2 * N.Nm ^ 2 := Nat.le_mul_of_pos_left _ hm
    calc ((ybSet sel mu cst L).ncard : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (2 * N.R.f * n) := by exact_mod_cast h1
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * n) := pow_le_pow_left₀ (by linarith) ggT _
      _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (2 * N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
      _ = Real.exp (2 * errUnit N (Pr.T u)) := by
        rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
        unfold errUnit
        push_cast
        ring
  exact ⟨key _, fun L _ => key L⟩

end GlobalTheory.CouplingCosetsS
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.UnfoldS

open GlobalTheory.TopStep GlobalTheory.LastSteps GlobalTheory.PadicUnfold GlobalTheory.PadicUnfold.Period GlobalTheory.ColNorms.Unfold

theorem locSmall_XiAt_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (P : rowSG Pr sel mu), LocSmall (Formalism.L2.Col.qOf P.1) (stdAt X.E (N.R.N i) P.1) (stdAt X.E (N.R.N (i + 1)) P.1) (XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) ((Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2)) := by
  refine ⟨2, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be P => ?_⟩
  obtain ⟨hvG, hpr, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hP : P.1 ∈ Pr.vGs := hvG _ P.2
  obtain ⟨g, -, hg, -, hg2, -⟩ := hpr _ hP
  have hom := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i (by omega) P (I.h i al P) (I.h (i + 1) be P)
  obtain ⟨hH, -, -, -, -, hsharp, hI, -⟩ := H
  have hPr : Pr.Ok := hH.2.2.2.2.2.2.2.2.2.1
  have hq : (Formalism.L2.Col.qOf P.1).Prime := hg ▸ hPr.g_prime g
  rw [← hg] at hg2
  have hs' := hI.stabG (i + 1) be P hP
  replace hom := hom (hI.stabG i al P hP) hs'
  unfold lamYat at hom hs'
  rw [if_pos hP] at hom hs'
  have hE := unfolding_smallHomFunction_levelPrime_bounded hq (c' := cOf N.R i) (c := cOf N.R (i + 1)) (by unfold cOf; omega) cst.A cst.B (cst.psi P)
    (fun a ha => by
      have := GlobalTheory.GO.ChRoot.psi_root hI.cst_ok P a (by rwa [hI.depthG P hP, pow_one])
      rwa [hI.depthG P hP, pow_one] at this) _ hom
  refine ⟨fun x hx => hE.1 x (right_ne_zero_of_mul hx), fun x z hz => ?_, fun σ x => ?_⟩
  · unfold XiAt E1at
    rw [hE.2.1 x z hz]
  · have hq1 : (1 : ℝ) ≤ Formalism.L2.Col.qOf P.1 := by exact_mod_cast hq.one_le
    unfold XiAt E1at
    rw [map_mul, norm_mul]
    have h1 := (norm_volN_inv_le (K := X.K) _ _ σ).trans (Nat.cast_le.2
      (relIndex_le hg2 N.R.k N.R.rS N.R.r N.R.t (N.R.N (i + 1)) (cOf N.R (i + 1)) _ hs'))
    unfold Jat lamYat
    rw [if_pos hP, if_pos hP, if_pos hsharp]
    refine (mul_le_mul h1 (hE.2.2 σ x) (norm_nonneg _) (Nat.cast_nonneg _)).trans ?_
    rw [Nat.cast_pow, ← pow_add]
    refine pow_le_pow_right₀ hq1 ?_
    have a1 := rank_le N.R (j := i) (by omega)
    have a2 := rank_le N.R (j := i + 1) (by omega)
    have a3 : cOf N.R i + 1 ≤ N.R.m := by unfold cOf; omega
    unfold NumDatum.Nm
    generalize N.R.N i + cOf N.R i = a at a1 ⊢
    generalize N.R.N (i + 1) + cOf N.R (i + 1) = b at a2 ⊢
    generalize N.R.N N.R.m = M at a1 a2 ⊢
    have b1 : b * b ≤ M * M := Nat.mul_le_mul a2 a2
    have b2 : b * a ≤ M * M := Nat.mul_le_mul a2 a1
    calc b * b + cOf N.R i * (b * a) ≤ M * M + cOf N.R i * (M * M) := by gcongr
      _ = (cOf N.R i + 1) * M ^ 2 := by ring
      _ ≤ (2 * N.R.m ^ 2) * M ^ 2 := Nat.mul_le_mul_right _ (by nlinarith)

end GlobalTheory.Core.Ht2.UnfoldS
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedEntry_typePrime_support_period_size : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (P : rowSG Pr sel mu), LocSmall (Formalism.L2.Col.qOf P.1) (stdAt X.E (N.R.N i) P.1) (stdAt X.E (N.R.N (i + 1)) P.1) (XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) ((Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2)) := by
  atlas_forward_decl GlobalTheory.Core.Ht2.UnfoldS.locSmall_XiAt_sharp
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.EntryDatumS

open GlobalTheory.ColNorms.EntryDatum

theorem smallDatum_xiEntry_sharp : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.unfoldedEntry_typePrime_support_period_size
  refine ⟨C, fun CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p' => ?_⟩
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hg : ∀ i, Pr.g i = N.g i := H.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (p : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j p P x
    have hP := h1 P.1 P.2
    unfold frsF
    rw [dif_pos hP]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ p.deco ⟨P.1, hP⟩).1 x
  have key := smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 p'.deco.1 p'.deco.2 (frsF sel mu p) (frsF sel mu p')
    (hfr p) (hfr p') (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P => XiAt Ch sel mu cst i P (I.h i al P) (I.h (i + 1) be P)) _
    (hC CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be)
  have e : ∏ P : rowSG Pr sel mu, (Formalism.L2.Col.qOf P.1 : ℝ) ^ (C * N.R.m ^ 2 * N.Nm ^ 2) =
      ((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    rw [Finset.prod_pow, ← Nat.cast_prod, h4, hg 0, hg 1]
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [e] at key
  exact key

end GlobalTheory.Core.Ht2.EntryDatumS
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size : ∃ C : ℕ, ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i + 2 < N.R.m → ∀ (al : I.β i) (be : I.β (i + 1)) (p : ChPt (R := N.R) sel mu u i) (p' : ChPt (R := N.R) sel mu u (i + 1)), SmallDatum (Sall sel mu u) p.deco.1.N p'.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiEntry Ch sel mu cst I i al be p p') (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) := by
  atlas_forward_decl GlobalTheory.Core.Ht2.EntryDatumS.smallDatum_xiEntry_sharp
end

section
section
noncomputable section

namespace GlobalTheory.Core.Ht2.DatOneS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem smallDatum_xiCpl1_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH al p₀ p Y
  obtain ⟨hrow, hG, hT, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH
  have hI : I.Ok Ch sel mu cst G (N.R.m - 2) := hH.2.2.2.2.2.2.1
  have hfr : ∀ {j : ℕ} (r : ChPt (R := N.R) sel mu u j) (P : rowSG Pr sel mu) x,
      frsF sel mu r P x ∈ r.deco.1.at P.1 ↔ x ∈ stdAt X.E (N.R.N j) P.1 := by
    intro j r P x
    have hP := hrow P.1 P.2
    simp only [frsF, hP, dif_pos]
    exact (GlobalTheory.ColNorms.liftFr_lifts X.E _ _ _ r.deco ⟨P.1, hP⟩).1 x
  have key := @GlobalTheory.ColNorms.DatOne.smallDatum_of_frames X.E X.K _ _ _ _ _ _ (Pr.vT u) _ _ (rowSG Pr sel mu) (fun a b => Classical.propDecidable (a = b))
    p₀.deco.1 p.deco (frsF sel mu p₀) (frsF sel mu p) (hfr p₀) (hfr p) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P => Formalism.L2.Col.qOf P.1) ?_ ?_
    (fun P x => PsiAt Ch sel mu cst (N.R.m - 2) P (I.h (N.R.m - 2) al P) x ((frsF sel mu p P).symm (repY Y))) (fun _ => 1) ?_
  · rw [Finset.prod_const_one] at key
    exact key
  · intro P
    obtain ⟨i, -, hq, -⟩ := hG P.1 (hrow P.1 P.2)
    show Formalism.L2.Col.qOf P.1 ∣ _
    rw [hq]
    refine Dvd.dvd.mul_left ?_ _
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · intro P hP
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hT P hP)
  · intro P
    have hm := hI.hm
    have h := GlobalTheory.T.movedDatum_small_typePrime_any_level CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hH (N.R.m - 2) (by omega) P
      (I.h (N.R.m - 2) al P) 1 (hI.stabG _ al P (hrow P.1 P.2)) (one_mem _)
    exact GlobalTheory.ColNorms.DatOne.locSmall_joinCol h _

end GlobalTheory.Core.Ht2.DatOneS

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (al : I.β (N.R.m - 2)) (p₀ : ChPt (R := N.R) sel mu u (N.R.m - 2)) (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (Y : Set (Sp X.E (N.R.N (N.R.m - 2 + 1)))), SmallDatum (Sall sel mu u) p₀.deco.1.N p.deco.1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) 1 := by
  atlas_forward_decl GlobalTheory.Core.Ht2.DatOneS.smallDatum_xiCpl1_sharp
end

section
section
noncomputable section

namespace GlobalTheory.Core.Ht2.LastDatumS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
open GlobalTheory.TopStep GlobalTheory.ColNorms.LastDatum

theorem smallDatum_xiCpl2_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (d : RowPt Pr N.R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N, SmallDatum (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hY
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hI := H.2.2.2.2.2.2.1
  have hT : TilOk Pr sel mu u := by
    refine tilOk_of hPr u fun P hP => ?_
    have hmu : mu = mu0 X.F X.E X.K Sg := H.2.2.2.2.1
    rw [hmu, twistPrimes_trivialTuple_empty sel Sg] at hP
    simp at hP
  have key := EntryDatum.smallDatum_prod (K := X.K) (S := Sall sel mu u) p.deco.1 (tilQ sel mu u d).1 (tilQ sel mu u d).2
    (frsF sel mu p) (tilFr hT d) (frsF_mem p) (fun P => (tilFr_isLiftFr hT d P).1)
    (fun P => by classical exact Finset.mem_union) (Pr.T u * (Pr.g 0 * Pr.g 1))
    (fun P hP => by rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ (h3 P hP)) (fun P => Formalism.L2.Col.qOf P.1)
    (fun P => by
      obtain ⟨j, -, hj, -⟩ := h2 P.1 (h1 P.1 P.2)
      rw [hj]
      refine Dvd.dvd.mul_left ?_ _
      fin_cases j
      · exact Dvd.intro _ rfl
      · exact Dvd.intro_left _ rfl)
    (fun P y => locTop Ch sel mu cst (N.R.m - 2) P y ((frsF sel mu p P).symm (repY Y))) (fun _ => 1)
    (fun P => locSmall_locTop hI.hm hI.cst_ok H.2.2.2.2.2.1 (h1 P.1 P.2) (repY_int p hY (h1 P.1 P.2)))
  rw [Finset.prod_const_one] at key
  convert key using 1
  funext x
  unfold XiCpl2
  simp only [locTop_tilFr]

end GlobalTheory.Core.Ht2.LastDatumS
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (p : ChPt (R := N.R) sel mu u (N.R.m - 2 + 1)) (d : RowPt Pr N.R sel mu), ∀ Y ∈ ybSet sel mu cst p.deco.1.N, SmallDatum (Sall sel mu u) p.deco.1.N (tilQ sel mu u d).1.N (Pr.T u * (Pr.g 0 * Pr.g 1)) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) 1 := by
  atlas_forward_decl GlobalTheory.Core.Ht2.LastDatumS.smallDatum_xiCpl2_sharp
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.IndexCountS

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv GlobalTheory.SymLevelDatum GlobalTheory.IndexCount

theorem card_index_le_sharp : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ j, j + 2 ≤ N.R.m → (Fintype.card (I.β j) : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H j hj
  obtain ⟨hvG, -, -, hprod, -⟩ := BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, -, hsh, hI, -⟩ := H
  have hq : ∀ P : HeightOneSpectrum (𝓞 X.E), Formalism.L2.Col.qOf P ≠ 0 := fun P h =>
    P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hgg : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have h1 : Fintype.card (I.β j) ≤ (Pr.g 0 * Pr.g 1) ^ (N.R.f * N.Nm ^ 2) := by
    rcases j with _ | i
    · obtain ⟨b, hb⟩ := hI.zero_uniq
      exact (Fintype.card_le_one_iff.2 fun a a' => (hb a).trans (hb a').symm).trans (Nat.one_le_pow _ _ hgg)
    · set n := N.R.N (i + 1) + cOf N.R (i + 1) with hn
      haveI : ∀ P : rowSG Pr sel mu, Finite (𝓞 X.E ⧸ P.1.asIdeal) := fun P => finite_res P.1
      let φ : I.β (i + 1) → ∀ P : rowSG Pr sel mu, Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal := fun b P =>
        resMat P.1 (Formalism.L2.Col.qOf P.1) (scE (N.R.N (i + 1)) fun i => i + 1) (I.h (i + 1) b P)
      have hφ : Function.Injective φ := by
        intro b b' hbb
        refine hI.inj i (by omega) b b' fun P => ?_
        have hP := hvG P.1 P.2
        have s1 := hI.stabG _ b P hP
        have s2 := hI.stabG _ b' P hP
        unfold lamYat at s1 s2
        rw [if_pos hP] at s1 s2
        refine ⟨1, Subgroup.one_mem _, (I.h (i + 1) b P)⁻¹ * I.h (i + 1) b' P, ?_, by group⟩
        unfold Jat
        rw [if_pos hP, hsh, if_pos rfl]
        exact mem_JGsym_of_cong _ _ (hq _) _ _ _ _ _ _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ s1) s2)
          (cong_of_resMat_eq _ _ (hq _) (GlobalTheory.TypePrimeUnif.intAt_div_qOf X Pr hX.ok hPr P.1 hP) s1 s2 (congrFun hbb P))
      have h2 := Nat.card_le_card_of_injective φ hφ
      have h3 : ∀ P : rowSG Pr sel mu, Nat.card (Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal) = Formalism.L2.Col.qOf P.1 ^ (n * n) := fun P => by
        rw [Nat.card_fun, Nat.card_prod, Nat.card_fin]
        rfl
      rw [Nat.card_eq_fintype_card, Nat.card_pi, Finset.prod_congr rfl fun P _ => h3 P, Finset.prod_pow, hprod, ← pow_mul] at h2
      refine h2.trans (Nat.pow_le_pow_right hgg (Nat.mul_le_mul_left _ ?_))
      have h4 : n ≤ N.Nm := by
        rw [hn]
        unfold NumDatum.Nm Ranks.N cOf
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ N.R.m by omega)
        rw [hd]
        have : i + 1 + d - 1 - (i + 1) ≤ d := by omega
        nlinarith [Nat.zero_le (d * N.R.t)]
      rw [sq]
      exact Nat.mul_le_mul h4 h4
  rw [hg 0, hg 1] at h1
  have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
  have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
  have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
  have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
  have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
  have he : N.R.f * N.Nm ^ 2 ≤ N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  calc (Fintype.card (I.β j) : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (N.R.f * N.Nm ^ 2) := by exact_mod_cast h1
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * N.Nm ^ 2) := pow_le_pow_left₀ (by linarith) ggT _
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
    _ = Real.exp (1 * errUnit N (Pr.T u)) := by
      rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
      unfold errUnit
      push_cast
      ring

end GlobalTheory.Core.Ht2.IndexCountS
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_matrixStep_indices_le_exp : ∃ C : ℝ, 0 ≤ C ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ j, j + 2 ≤ N.R.m → (Fintype.card (I.β j) : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  atlas_forward_decl GlobalTheory.Core.Ht2.IndexCountS.card_index_le_sharp
end

section
namespace GlobalTheory.Core.Ht2.StepRowsS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

theorem weights_rows : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (W.lamTrue u i τ) (W.nuW u (i + 1) τ) (W.lamTrue u (i + 1) τ)) ∧ ∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((W.nuW u (i + 1) (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ hyp i hi
  obtain ⟨-, hW, -, -, -, -, -, -, hS⟩ := hyp
  refine ⟨fun τ => StepRows.stepWeights W u hi τ fun l => ?_, fun z l => StepRows.nuW_eq_nu N W pl u δ hW hi z l⟩
  obtain ⟨z, rfl⟩ := pl.surjective τ
  have h1 := StepRows.nuW_eq_nu N W pl u δ hW hi z l
  have h2 := (hS.2.2.2.2.1 (i + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) z l.1 l.2).1
  rw [← h1] at h2
  exact_mod_cast h2

end GlobalTheory.Core.Ht2.StepRowsS
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.ScalarModulusS

theorem norm_muInvDet_zero_or_one : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ i, i < N.R.m → ∀ (n : ℕ) (L : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)) (σ : X.K →+* ℂ), ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 0 ∨ ‖σ (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr)‖ = 1 := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h i hi n L fr σ
  obtain ⟨hH, -, ⟨-, hσ, -, ⟨eta, ht⟩, -, hsel⟩, -, hmu, -, hI, -, -⟩ := h
  obtain ⟨-, -, -, -, -, -, hX, -, -, hPr, -⟩ := hH
  rw [← hσ] at ht
  refine Or.inr (GlobalTheory.ScalarModulus.norm_muInvDet hX.ok hPr hsel (fun P => ?_) ht hI hi L fr σ)
  classical
  subst hmu
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · have h0 := twistPrimes_trivialTuple_empty sel Sg
    exact absurd (h0 ▸ h) (Finset.notMem_empty _)

end GlobalTheory.ScalarModulusS
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

namespace GlobalTheory.Core.Ht2.AAUnitS

theorem aaUnit_bad_sharp : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ h B P hP
  have hcond := h.1.pr_cond
  obtain ⟨⟨-, -, -, hcc, -, -, -, -, -, hPr, -⟩, -, -, -, hmu, -⟩ := h
  subst hmu
  obtain ⟨l, hl, hlP, hd⟩ := GlobalTheory.ColNormsUnit.exists_prime hPr sel u P hP
  rw [hcond] at hd
  refine GlobalTheory.AAUnitAway.locP_AA D X s _ dl B χ cD P l hl ?_ ?_ hlP ?_
  · intro hs
    exact hd (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  · rintro rfl
    exact hd ((dvd_mul_left _ _).mul_right _)
  · rw [hcc, Ideal.absNorm_top]
    exact Nat.coprime_one_left _

end GlobalTheory.Core.Ht2.AAUnitS
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodLatticeIdeal_trivial_at_badPrimes : ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, (ambOf s B χ cD).AAUnit (Sall sel mu u) := by
  atlas_forward_decl GlobalTheory.Core.Ht2.AAUnitS.aaUnit_bad_sharp
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2.KernelS

theorem kernel_le_sharp (hB : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound) (hT : FamilyTie) (hV : FamilyVectors) (hL : PeriodLattices)
    (hR : CosetRefinement) (hP : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod) (C : ℕ) : ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl,
      FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ i j, j = i + 1 → i < N.R.m →
      ∀ (L : Submodule (𝓞 X.E) (Sp X.E (N.R.N i))) (fr : Frs X.E (N.R.N i) (rowSG Pr sel mu))
        (L' : Submodule (𝓞 X.E) (Sp X.E (N.R.N j))) (fr' : Frs X.E (N.R.N j) (rowSG Pr sel mu)), IsSdLat L → IsSdLat L' →
      ∀ Ξ : HomE X.E (N.R.N i) (N.R.N j) → X.K, SmallDatum (Sall sel mu u) L L' (Pr.T u * (Pr.g 0 * Pr.g 1)) Ξ
        (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) →
      ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ),
        CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) (W.lamTrue u i) (W.lamTrue u j)
          (kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst)
            (cBof sel mu cst u) L fr L' fr' Ξ)
          (Real.exp (kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
            (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1)) := by
  obtain ⟨CK, hCK, hnum⟩ := GlobalTheory.T.exists_jetBlockBound_le_exp_kernelBound C
  refine ⟨CK, hCK, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD i j hj hi L fr L' fr' hL1 hL2 Ξ hΞ M _ hM ρ
  subst hj
  have H' := H
  obtain ⟨hHost, hWt, hCh, hAn, hmu, hsh, hI, hSz, hRows⟩ := H'
  obtain ⟨trd, -, -, -, tf, -, tE, -, tcc⟩ := GlobalTheory.T.numDatum_numbers_eq_host_of_compatible D N X s Pr hHost
  obtain ⟨-, -, -, -, hpsi, hadm, hX, hs, -, hPr, -, -, hg, -⟩ := hHost
  obtain ⟨-, -, -, hprod, hTodd, hgodd, hS⟩ := GlobalTheory.Core.Ht2.BadPrimesS.bad_primes_sharp CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨hstep, hnu⟩ := GlobalTheory.Core.Ht2.StepRowsS.weights_rows CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi
  have hcrv : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨tcc, hAn.1⟩
  have hY := GlobalTheory.T.kernelConstant_exponents_finite D B.γ₀ B.kc
  have hev : ∀ l, Even (N.R.N l) := fun l => by
    unfold Ranks.N
    exact N.R.k_even.add ((N.R.t_odd.add_one).mul_left l)
  have hlt : N.R.N i < N.R.N (i + 1) := by
    unfold Ranks.N
    nlinarith
  obtain ⟨hAdm, hbase⟩ := GlobalTheory.T.normalisedFamily_standardLattices_eq_baseVector D _ dl B χ hAn.2.1 (hV D _ dl B χ hadm hpsi tcc hAn.1 hAn.2.1 hY) _ _ (hev i) (hev (i + 1))
  have hE0 := hT D _ dl B χ hadm hpsi tcc hAn.1 hAn.2.1 hY _ B.t0 _ _ _ _ hAdm
  rw [hbase] at hE0
  have hgpos : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have hfpos : 0 < N.R.f := by unfold Ranks.f Ranks.n; positivity
  have hBpos := hI.cst_ok.B_pos
  have hcA : cAof sel mu cst = (Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.A) := by unfold cAof; rw [hprod, pow_mul]
  have hcB : cBof sel mu cst u = Pr.T u * (Pr.g 0 * Pr.g 1) * (Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.B - 1) := by
    unfold cBof
    have h1 : N.R.f * cst.B = (N.R.f * cst.B - 1) + 1 := by
      have := Nat.mul_pos hfpos hBpos
      omega
    rw [hprod, ← pow_mul]
    conv_lhs => rw [h1]
    ring
  have hodd : Odd (cAof sel mu cst * cBof sel mu cst u) := by
    have h1 : Odd (Pr.g 0 * Pr.g 1) := (hgodd 0).mul (hgodd 1)
    rw [hcA, hcB]
    exact h1.pow.mul ((hTodd.mul h1).mul h1.pow)
  have hInd := hR X (ambOf s B χ cD) _ _ (Sall sel mu u) _ hX.ok (fun P hP => (hS P hP).2) hodd
    (hL D X s _ dl B χ cD hX.ok hs hadm hpsi tcc hAn.1 hAn.2.1 hAn.2.2 hY _ _ (Sall sel mu u) (hev i) (hev (i + 1))
      (fun P hP => (hS P hP).1) (GlobalTheory.T.periodLatticeIdeal_trivial_at_badPrimes CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B))
  have hJ := hFD i hi
  have hc0 : ∀ τ, cD τ ≠ 0 := (GlobalTheory.T.mean_logMetric_generator_eq_meanPeriod D _ dl cD hcrv (hP D _ dl tcc hAn.1) hAn.2.2).1
  have hsc : ‖((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1))
      (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L fr *
        (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu i) (muAt Ch sel mu cst i) L' fr')⁻¹)‖ ≤ 1 := by
    rw [map_mul, map_inv₀, norm_mul, norm_inv]
    rcases GlobalTheory.ScalarModulusS.norm_muInvDet_zero_or_one CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi _ L fr
      ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) with h1 | h1 <;>
    rcases GlobalTheory.ScalarModulusS.norm_muInvDet_zero_or_one CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi _ L' fr'
      ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) with h2 | h2 <;> rw [h1, h2] <;> norm_num
  unfold stepC
  rw [hcB] at hInd hJ ⊢
  have key := block hB D X s _ dl B χ cD _ hX.ok hs hcrv B.t0 hc0 _ _ hlt ((hev i).mul_right _) hE0
    (W.lamTrue u i) (W.nuW u (i + 1)) (W.lamTrue u (i + 1)) hstep (Sall sel mu u) (rowSG Pr sel mu) (cAof sel mu cst)
    (Pr.T u * (Pr.g 0 * Pr.g 1)) ((Pr.g 0 * Pr.g 1) ^ (N.R.f * cst.B - 1)) (by rw [hcA]; positivity)
    (Nat.mul_pos (hPr.T_prime u).pos hgpos) (by positivity) hInd hJ sel (mUof Ch mu i) (muAt Ch sel mu cst i) L fr L' fr' hL1 hL2
    Ξ _ hΞ M hM.1 ρ hM.2.1 hM.2.2.1 (hM.2.2.2 i hi) hsc
  have hn := hnum N δ (Pr.T u) i X.Tau pl (W.nuW u (i + 1)) (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N i) (N.R.N (i + 1))) hi (hPr.T_prime u).two_le (fun τ => (hstep τ).1) hnu
  intro x
  refine (key x).trans (mul_le_mul_of_nonneg_right ?_ ?_)
  · refine le_trans (le_of_eq ?_) hn
    simp only [supConst, tf, tE, ← trd, hg, Equiv.apply_symm_apply]
  · exact sqAt_nonneg _ _ _

end GlobalTheory.Core.Ht2.KernelS
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ B : Base D D.host.ccK dl, FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ i j, j = i + 1 → i < N.R.m → ∀ (L : Submodule (𝓞 X.E) (Sp X.E (N.R.N i))) (fr : Frs X.E (N.R.N i) (rowSG Pr sel mu)) (L' : Submodule (𝓞 X.E) (Sp X.E (N.R.N j))) (fr' : Frs X.E (N.R.N j) (rowSG Pr sel mu)), IsSdLat L → IsSdLat L' → ∀ Ξ : HomE X.E (N.R.N i) (N.R.N j) → X.K, SmallDatum (Sall sel mu u) L L' (Pr.T u * (Pr.g 0 * Pr.g 1)) Ξ (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2)) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), CoefOpLe ((ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1)) (W.lamTrue u i) (W.lamTrue u j) (kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) L fr L' fr' Ξ) (Real.exp (kernelBound_sq N δ (Pr.T u) CK j (fun z => logOmAt B cD M ρ (s.iT (pl z))) (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1))  := by
  atlas_forward_decl GlobalTheory.Core.Ht2.KernelS.kernel_le_sharp
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.Core.Ht2

theorem factors_leS : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  intro hB hT hV hL hR hP
  obtain ⟨Cd, hdat⟩ := GlobalTheory.T.matrix_entry_finite_datum_bounded_level_size
  obtain ⟨C₁, hC₁, hker⟩ := GlobalTheory.T.chainKernel_bound_at_embedding_anyLevelPrime hB hT hV hL hR hP Cd
  obtain ⟨Cc, hCc, hcl⟩ := GlobalTheory.ChainClassNumbersS.classNumbers_leS
  obtain ⟨Ci, hCi, hidx⟩ := GlobalTheory.T.card_matrixStep_indices_le_exp
  obtain ⟨Cy, hCy, hyb⟩ := GlobalTheory.CouplingCosetsS.ncard_ybSet_le
  refine ⟨C₁ + (Cc + Ci + Cy), by positivity, ?_⟩
  intro CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B b hY hK hF hE hFD M _ hM ρ
  have hPr : Pr.Ok := H.1.2.2.2.2.2.2.2.2.2.1
  have hU := errUnit_nonneg N (hPr.T_prime u).one_lt.le
  have hm := N.R.two_le_m
  set U := errUnit N (Pr.T u) with hUdef
  set σ : X.K →+* ℂ := (ρ : M →+* ℂ).comp (s.σ₀.codRestrict M hM.1) with hσ
  set Q := KerChain.ofCol W Ch sel mu cst I
    (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE with hQ
  set kb : ℕ → ℝ := fun j => kernelBound_sq N δ (Pr.T u) C₁ j (fun z => logOmAt B cD M ρ (s.iT (pl z)))
    (logThAt B M ρ (N.R.N (j - 1)) (N.R.N j)) 1 1 1 1 with hkb
  have hlift : ∀ j, kb j + 2 * ((Cc + Ci + Cy) * U) ≤
      liftBound_sq N s W Ch sel mu cst I B cD pl u δ (C₁ + (Cc + Ci + Cy)) M ρ j := fun j =>
    kernelBound_ge N δ _ _ _ j _ _ _ _ _ _
  have hpos : ∀ {n : ℕ} (lam : X.Tau → DomWeight n),
      ((Matrix.of fun i j => pairVr X.emb lam 1 (bVV X.K lam i) (bVV X.K lam j)).map
        (placeUnder s.σ₀ hM.1 ρ).embedding).PosSemidef := fun lam => (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb _ lam _).1
  have hsq := fun {n : ℕ} (lam : X.Tau → DomWeight n) => (GlobalTheory.T.coefficientGram_posSemidef_and_normAtPlace X.E X.K X.Tau X.emb n lam σ).2
  have hk := hker CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H B hFD
  obtain ⟨hc1, hc2, -⟩ := hcl CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hi1 := hidx CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  have hfam : ∀ j, ∀ φ : (Q.F j).Forms, 0 ≤ (famIpAt (Q.F j) (Q.hF j) (placeUnder s.σ₀ hM.1 ρ) φ φ).re := by
    intro j φ
    unfold famIpAt GSD.ipAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b' _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    refine mul_nonneg (by positivity) ?_
    exact (sqAt_nonneg (W.lamTrue u j) σ _).trans_eq (hsq (W.lamTrue u j) _).symm
  have hone : (1 : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (Cd * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by
    have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
    have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
    exact one_le_pow₀ (one_le_mul_of_one_le_of_one_le h0 h1)
  refine ⟨fun i hi φ => ?_, fun φ => ?_⟩
  · have h1 := GlobalTheory.T.sq_norm_classSumMatrix_le_cauchySchwarz X.K Q i (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (i + 1))) (Real.exp (Cc * U)) (Real.exp (Cc * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (fun _ => hpos (W.lamTrue u i))
      (fun _ => hpos (W.lamTrue u (i + 1))) (hc1 i (by omega)) (hc1 (i + 1) (by omega)) (by
        intro al be p p' x
        have h2 := hk i (i + 1) rfl (by omega) _ (frsF sel mu p) _ (frsF sel mu p') ⟨p.deco.2.lat, p.deco.2.uni⟩
          ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ (hdat CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H i hi al be p p') M hM ρ x
        have e : (Q.kk i al be).k p p' = matK W Ch sel mu cst I (chTh W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2)) i al be p p' := by
          exact congrArg (fun k : ClsKer _ _ => k.k p p') (dif_pos (show i < N.R.m - 2 by omega))
        rw [e]
        exact (hsq (W.lamTrue u (i + 1)) _).trans_le (h2.trans_eq (congrArg _ (hsq (W.lamTrue u i) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam i φ))
    have b1 : (Fintype.card (Q.F i).β : ℝ) ≤ Real.exp (Ci * U) := hi1 i (by omega)
    have b2 : (Fintype.card (Q.F (i + 1)).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (i + 1) (by omega)
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) * Real.exp (kb (i + 1)) := by gcongr
      _ ≤ _ := by
        simp only [← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (hlift _))
        nlinarith [mul_nonneg hCy hU]
  · have hNle : N.R.N (N.R.m - 2 + 1) ≤ N.Nm := by
      unfold NumDatum.Nm Ranks.N
      have : N.R.m - 2 + 1 ≤ N.R.m := by omega
      gcongr
    have h1 := GlobalTheory.T.coupled_class_sum_cauchy_schwarz X.K Q (placeUnder s.σ₀ hM.1 ρ) (Real.exp (kb (N.R.m - 2 + 1))) (Real.exp (kb N.R.m))
      (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cc * U)) (Real.exp (Cy * U))
      (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le
      (fun _ => hpos (W.lamTrue u (N.R.m - 2))) (hpos (W.lamTrue u (N.R.m - 2 + 1))) (hpos (W.lamTrue u N.R.m))
      (hc1 (N.R.m - 2) (by omega)) (hc1 (N.R.m - 2 + 1) (by omega) b) hc2
      (fun p => (hyb CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H _ hNle).2 _ p.deco.2.lat) (by
        intro al p₀ p Y hYm x
        have h2 := hk (N.R.m - 2) (N.R.m - 2 + 1) rfl (by omega) _ (frsF sel mu p₀) _ (frsF sel mu p)
          ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩ ⟨p.deco.2.lat, p.deco.2.uni⟩ _
          ((GlobalTheory.T.firstCoupledKernel_finiteDatum_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H al p₀ p Y).mono hone) M hM ρ x
        have e : (Q.cp al).k1 p₀ p Y = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2) (W.lamTrue u (N.R.m - 2 + 1)))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p₀.deco.1.N (frsF sel mu p₀) p.deco.1.N (frsF sel mu p)
            (XiCpl1 Ch sel mu cst I (N.R.m - 2) al p₀ p Y) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2)) _).symm))) (by
        intro al p d Y hYm x
        have h2 := hk (N.R.m - 2 + 1) N.R.m (by omega) (by omega) _ (frsF sel mu p) _ (frsT sel mu u d)
          ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _
          ((GlobalTheory.T.lastKernelFiniteDatum_bounded_level_size CY D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H p d Y hYm).mono hone) M hM ρ x
        have e : (Q.cp al).k2 p Y d = kerOf (stepC W Ch sel mu cst (ambOf s B χ cD) u (N.R.m - 2 + 1) (W.lamTrue u N.R.m))
            (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) p.deco.1.N (frsF sel mu p) (tilQ sel mu u d).1.N
            (frsT sel mu u d) (XiCpl2 Ch sel mu cst (N.R.m - 2) p Y d) := if_pos hYm
        rw [e]
        exact (hsq (W.lamTrue u N.R.m) _).trans_le
          (h2.trans_eq (congrArg _ (hsq (W.lamTrue u (N.R.m - 2 + 1)) _).symm))) φ
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ (hfam _ φ))
    have b1 : (Fintype.card (Q.F Q.n).β : ℝ) ≤ Real.exp (Ci * U) := hi1 (N.R.m - 2) (by omega)
    have e1 : N.R.m - 2 + 1 = N.R.m - 1 := by omega
    calc _ ≤ Real.exp (Ci * U) * Real.exp (Cc * U) * Real.exp (Cc * U) ^ 2 * Real.exp (Cc * U) * Real.exp (Cy * U) ^ 2 *
          Real.exp (kb (N.R.m - 2 + 1)) * Real.exp (kb N.R.m) := by gcongr
      _ ≤ _ := by
        simp only [sq, ← Real.exp_add]
        refine Real.exp_le_exp.2 (le_trans ?_ (add_le_add (hlift _) (hlift _)))
        rw [e1]
        nlinarith [mul_nonneg hCy hU, mul_nonneg hCi hU]

end GlobalTheory.Core.Ht2
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms GlobalTheory.CoreHt GlobalTheory.Core.Ht2
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norms_matrixSteps_coupledFactor_bounded_anyLevelPrime : GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.BlockBound → FamilyTie → FamilyVectors → PeriodLattices → CosetRefinement → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod → ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (CY : ℝ) (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), HypS CY N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ (B : Base D D.host.ccK dl) (b : I.β (N.R.m - 2 + 1)) (hY : YbHyp (R := N.R) sel mu cst I u (N.R.m - 2) b) (hK : KerEquivC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch)) (hF : ∀ j, (chF W sel mu I u j).Ok) (hE : (evGSD W Ch sel mu (rPsymF Ch) u).Ok), FieldOfDefinition W sel mu cst u (ambOf s B χ cD) → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (hM : ThetaFieldData B cD s.σ₀ N.R M) (ρ : M →ₐ[ℚ] ℂ), (∀ i, i + 2 < N.R.m → StepBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) i (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (i + 1))) ∧ CplBound_sq (KerChain.ofCol W Ch sel mu cst I (chKerC W Ch sel mu cst I (ambOf s B χ cD) u (N.R.m - 2) b hY (rPsymF Ch) hK) hF hE) (placeUnder s.σ₀ hM.1 ρ) (liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ (N.R.m - 1) + liftBound_sq N s W Ch sel mu cst I B cD pl u δ CK M ρ N.R.m)  := by
  atlas_forward_decl GlobalTheory.Core.Ht2.factors_leS
end
