import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SupportProduct
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroSDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpCount
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpOrd
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpPiSub
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSpSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPCuspSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPProdIrr

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
namespace P_spTop
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end P_spTop
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem step_spTop_alt (G : Grp k n) : G.Step_spTop_alt := by
  intro hLat hUniq hCount hLift hTw hRes hPiEta hOrd hPiSub hSupp hCusp hProd hTen L V _ _ π hπs hπi Y iY mY τ hτs hτi hτd hsub
  have hc : ∀ a, ∃ μ' : Fin (G.d a) → kˣ →* ℂˣ,
      (∀ j, IsSmoothChar (μ' j) ∧ ∀ u : kˣ, valuation k (u : k) = 1 → μ' j u = G.μ a u) ∧
        IsCuspSupport (τ a) (fun _ => 1) (fun j => detRep (Fin 1) (μ' j)) :=
    fun a => hCusp L.loc k (G.d a) (Y a) (τ a) (hτs a) (hτi a) (G.μ a) (G.smooth a) (hτd a)
  choose ν hν hνc using hc
  have hνs : ∀ a j, IsSmoothChar (ν a j) := fun a j => (hν a j).1
  have hνr : ∀ a j, res (ν a j) = res (G.μ a) := fun a j => P_spTop.res_eq (hν a j).2
  have htw := fun a => hTw Y τ a (hτs a) (hτi a) (hτd a)
  have hPi : (multiProd G.e (G.twD τ)).IsIrreducible :=
    hProd hCusp L.loc k G.s n G.d G.hd Y (G.twD τ) (fun a => (htw a).1) (fun a => (htw a).2.1) G.μ G.smooth
      (fun a => (htw a).2.2) (fun b c hbc => P_spTop.exists_unit_ne (G.dist b c hbc))
  have hπI := hSupp hOrd L V π hπs hπi Y τ hτs hτi ν hνs hνc hsub
  have hPI := hPiSub hOrd L Y τ hτs hτi ν hνs hνc hPi
  obtain ⟨hfd, hle⟩ := hCount L (G.cOf ν) (P_spTop.isSmoothChar_cOf G ν hνs) (hRes ν hνr)
  have hπη : G.HasEtaVec (jacU G.e π) := by
    obtain ⟨v, hv0, hv⟩ := hTen k G.s G.d Y τ G.μ hτd
    refine hLift _ _ (jacU G.e π) (piTensor τ) (isSmooth_jacU G.e hπs) hsub ⟨v, hv0, fun m hm => ?_⟩
    have hm' := hm
    rw [leviK, Subgroup.mem_pi] at hm'
    exact hv m fun a => hm' a (Set.mem_univ a)
  have hPη := hPiEta hLift Y τ hτs hτd
  obtain ⟨e⟩ := hUniq hLat _ (prinSeries (G.cOf ν)) (P_spTop.isSmooth_prinSeries _) hfd hle _ _ π
    (multiProd G.e (G.twD τ)) hπi hPi hπI hPI hπη hPη
  exact ⟨Y, iY, mY, G.twD τ, fun a => (htw a).1, fun a => (htw a).2.1, fun a => (htw a).2.2, ⟨e⟩⟩
end UpperTheory.TNZ.Grp
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spCount
section Abstract
variable {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W]
end Abstract
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ}
variable (G : Grp k n)
end Local
end UpperTheory.TNZ.Grp.P_spCount
namespace UpperTheory.TNZ.Grp
open P_spCount
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open scoped Classical in
set_option maxHeartbeats 800000 in
theorem step_spCount_alt {n : ℕ} (G : Grp k n) : G.Step_spCount_alt := by
  intro hL c hc hres
  have hE : G.etaSp (jacU G.e (prinSeries c)) =
      eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta (jac G.e (parInd (points (Fin n)) (ρc c))) :=
    eS_jacU_eq G.e (parInd (points (Fin n)) (ρc c)) G.eta
  obtain ⟨N, b, hb⟩ := (hL.loc.geo k).1 (Fin n) (Fin G.s) (Fin n) (fun _ => Unit)
    (fun a => Fin (G.d a)) (points (Fin n)) G.e
  obtain ⟨S, hmono, h0, hN, hS⟩ := hb ℂ (ρc c) (isSmooth_ρc c hc)
  obtain ⟨fr⟩ : Nonempty (∀ t : Fin N, ∀ i, (Σ j, Fin ((b t).1 i j)) ≃ (fun _ : Fin n => Unit) i) :=
    ⟨fun t => (b t).nonempty_rows.some⟩
  obtain ⟨gc⟩ : Nonempty (∀ t : Fin N, ∀ j, (Σ i, Fin ((b t).1 i j)) ≃ (fun a : Fin G.s => Fin (G.d a)) j) :=
    ⟨fun t => (b t).nonempty_cols.some⟩
  have hr : ∀ t : Fin N, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (subQuot (S t.succ) (S t.castSucc))) ≤ Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a)))
        G.eta (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := by
    intro t
    have e : Nonempty ((subQuot (S t.succ) (S t.castSucc)).Equiv
        (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) := hS t (fr t) (gc t)
    exact rank_eS_le_of_equiv _ _ e.some
  have hr1 : ∀ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) ≤
        ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := by
    intro t
    split_ifs with hP
    · refine (rank_eS_le (gc t) (cellRep G c (b t) (fr t) (gc t)) G.eta).trans
        ((rank_quotient_le _).trans (le_of_eq ?_))
      rw [Module.rank_self, Nat.cast_one]
    · refine (rank_eS_eq_zero _ _ _ ?_).trans_le zero_le
      intro F hF
      by_contra hne
      apply hP
      intro i a h
      by_contra hab
      apply G.dist a (G.bl i) hab
      refine MonoidHom.ext fun w => ?_
      have h1 := cell_char G c (b t) (fr t) (gc t) F hF hne i a h w
      have h2 : c i (unitIncl k w) = G.μ (G.bl i) (unitIncl k w) := DFunLike.congr_fun (hres i) w
      exact h1.symm.trans h2
  have hsum : ∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) ≤ 1 := by
    rw [← Finset.card_filter]
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
    exact b.injective (good_unique G ht ht')
  have hrank : Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 := by
    calc _ ≤ ∑ t, Module.rank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
          (smInd (relParab k (gc t)) (cellRep G c (b t) (fr t) (gc t)))) :=
          rank_le_of_filtration _ _ S hmono h0 hN _ hr
      _ ≤ ∑ t : Fin N, ((if Good G (b t) then 1 else 0 : ℕ) : Cardinal) := Finset.sum_le_sum fun t _ => hr1 t
      _ = ((∑ t : Fin N, (if Good G (b t) then 1 else 0 : ℕ) : ℕ) : Cardinal) := (Nat.cast_sum _ _).symm
      _ ≤ 1 := by exact_mod_cast hsum
  haveI : Module.Free ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) := Module.Free.of_divisionRing ℂ _
  have hfin : FiniteDimensional ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.one_lt_aleph0)
  have hfr : Module.finrank ℂ ↥(eS (leviK k (fun a : Fin G.s => Fin (G.d a))) G.eta
      (jac G.e (parInd (points (Fin n)) (ρc c)))) ≤ 1 :=
    Module.finrank_le_of_rank_le (n := 1) (by rw [Nat.cast_one]; exact hrank)
  rw [hE]
  exact ⟨hfin, hfr⟩
end UpperTheory.TNZ.Grp
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spOrd
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end UpperTheory.TNZ.Grp.P_spOrd
namespace UpperTheory.TNZ.Grp
open UpperTheory.TNZ.Grp.P_spOrd GlobalTheory.LocGL.SupportRing
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
theorem step_spOrd_alt : _root_.UpperTheory.TNZ.Grp.Step_spOrd_alt (k := k) (n := n) := by
  intro hL V _ _ π hs hi c hc σ h
  obtain ⟨Z, Ψ, -, hΨ, -⟩ := hL.loc.zel k
  obtain ⟨hp1, e1⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c (σ i))) (fun i => isSmooth_detRep1 (hc (σ i)))
    (fun i => hasFiniteLength_detRep1 (c (σ i)))
  obtain ⟨hp2, e2⟩ := multiProd_cls (Ψ := Ψ) hΨ (d := fun _ : Fin n => 1) (X := fun _ => ℂ) (sum_one n)
    (fun i => detRep (Fin 1) (c i)) (fun i => isSmooth_detRep1 (hc i))
    (fun i => hasFiniteLength_detRep1 (c i))
  have hcl : clsGL _ hp1 = clsGL _ hp2 := by
    apply Ψ.injective
    rw [e1, e2]
    exact Equiv.prod_comp σ (fun i => Ψ (clsGL (detRep (Fin 1) (c i)) (hasFiniteLength_detRep1 (c i))))
  have h1 := h.trans (prin_sub_multi (fun i => c (σ i)))
  have h2 := clsGL_of_pos hp1 hs hi h1
  rw [hcl] at h2
  exact (isSubquotient_of_clsGL_ne hp2 hs hi h2.ne').trans
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries _ c)
end UpperTheory.TNZ.Grp
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp.P_spPiSub
end UpperTheory.TNZ.Grp.P_spPiSub
namespace UpperTheory.TNZ.Grp
open P_spPiSub
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem step_spPiSub_alt {n : ℕ} (G : Grp k n) : G.Step_spPiSub_alt := by
  intro hOrd hL Y _ _ τ _ _ ν hν hc hI
  let χ : Fin G.s → kˣ →* ℂˣ := fun a => absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  have hsupp : ∀ a, HasSupport (G.twD τ a)
      (Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) := by
    intro a
    have h1 := (hasSupport_of_isCuspSupport (hc a)).tw (χ a) (hχ a)
    rw [Multiset.map_map] at h1
    convert h1 using 2
    · rfl
    · rename_i j _
      exact (IrrGL.tw_ofChar (ν a j) (χ a) (hν a j) (hχ a)).symm
  have hcOf : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hS := SupportRing.hasSupport_multiProd hL.loc.zel G.hd (G.twD τ) (fun a => (hsupp a).isSmooth)
    (fun a => (hsupp a).isIrreducible) hsupp hI
  have hsum : (∑ a, Finset.univ.val.map fun j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a))) =
      Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i) :=
    sum_map_univ G.e (fun a j => IrrGL.ofChar (ν a j * χ a) ((hν a j).mul (hχ a)))
  obtain ⟨h, x, hx, -, -, e', he⟩ := hS
  rw [hsum] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x (fun i => IrrGL.ofChar (G.cOf ν i) (hcOf i)) hx
  obtain rfl : x = fun b => IrrGL.ofChar (G.cOf ν (σ b)) (hcOf _) := funext fun b => (hσ b).symm
  have hn : h = n := by simpa using Fintype.card_congr σ
  subst hn
  let φ := multiProdEquiv e' fun b =>
    (equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ b)) (hcOf _))).symm
  have hsq : IsSubquotient (multiProd G.e (G.twD τ)) (prinSeries fun b => G.cOf ν (σ b)) :=
    (he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)).trans
      (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e' _)
  exact hOrd hL _ _ (isSmooth_parInd _ _) hI _ hcOf σ hsq
end UpperTheory.TNZ.Grp
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.Grp
namespace P_spSupp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} (G : Grp k n)
end P_spSupp
open P_spSupp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ}
theorem step_spSupp_alt (G : Grp k n) : G.Step_spSupp_alt := by
  intro hOrd hLit V _ _ π hπs hπi Y _ _ τ hτs hτi ν hν hcs hjac
  have hG := hLit.loc.geo
  have hZ := hLit.loc.zel
  have hBZ := hLit.loc.bz
  have hs' : ∀ a, IsSmooth (G.twD τ a) := fun a =>
    isSmooth_twist (hτs a) (isSmoothChar_absPow _).detChar
  have hi' : ∀ a, (G.twD τ a).IsIrreducible := fun a => GlobalTheory.LocGL.isIrreducible_twist (hτi a) _
  have hτJ : (piTensor (G.twD τ)).IsIrreducible := isIrreducible_piTensor_twD G hBZ τ hs' hi'
  have hJs : IsSubquotient (piTensor (G.twD τ)) (jac G.e π) := by
    rw [piTensor_twD_eq]
    exact GlobalTheory.LocGL.isSubquotient_twist hjac _
  obtain ⟨s, hsπ⟩ := GlobalTheory.LocGL.SupportRing.exists_hasSupport hZ (IrrGL.of π hπs hπi)
  have hsπ' : HasSupport π s := hsπ.of_equiv (IrrGL.equivOf π hπs hπi).symm
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (G.d j)) k), IsSubquotient y.ρ
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j) :
        Representation ℂ (GL (Fin (G.d j)) k) _) ∧ Nonempty ((G.twD τ j).Equiv y.ρ) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      ((piTensor (G.twD τ)).comp (MonoidHom.mulSingle (fun j => GL (Fin (G.d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτJ)
    have h1 : IsSubquotient υ (G.twD τ j) :=
      GlobalTheory.LocGL.SupportUnique.isSubquotient_factor (G.twD τ) j hυ hυs
    exact ⟨⟨X, υ, h1.isSmooth (hs' j), hυ⟩, hυs,
      GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hυ (hi' j) h1⟩
  choose y hy hyE using hy
  obtain ⟨t, ht, hst⟩ := GlobalTheory.LocGL.SupportUnique.exists_sum_of_jac hG hZ hsπ' G.e hτJ hJs y hy
  have hsm : ∀ a j,
      IsSmoothChar (ν a j * absPow k (-((modExp (fun b : Fin G.s => Fin (G.d b)) a : ℂ) / 2))) :=
    fun a j => (hν a j).mul (isSmoothChar_absPow _)
  have htj : ∀ j, t j = Finset.univ.val.map fun i => IrrGL.ofChar _ (hsm j i) := by
    intro j
    obtain ⟨φ⟩ := hyE j
    refine GlobalTheory.LocGL.SupportUnique.eq_of_hasSupport hG hZ (G.d j)
      (IrrGL.of (G.twD τ j) (hs' j) (hi' j)) rfl _ _ ?_ ?_
    · exact ((ht j).of_equiv φ.symm).of_equiv (IrrGL.equivOf _ _ _)
    · exact (hasSupport_twD G τ ν hν hcs j (hsm j)).of_equiv (IrrGL.equivOf _ _ _)
  have hc : ∀ i, IsSmoothChar (G.cOf ν i) := fun i => (hν _ _).mul (isSmoothChar_absPow _)
  have hsF : s = Finset.univ.val.map fun i => IrrGL.ofChar (G.cOf ν i) (hc i) := by
    rw [hst, Finset.sum_congr rfl fun j _ => htj j]
    exact sum_map_univ G.e _ _ fun a j => IrrGL.ofChar_inj.2 (by
      unfold Grp.cOf
      rw [Equiv.symm_apply_apply])
  obtain ⟨h, x, hx, -, -, e, he⟩ := hsπ'
  rw [hsF] at hx
  obtain ⟨σ, hσ⟩ := exists_equiv_of_map_eq x _ hx
  obtain rfl : x = fun a => IrrGL.ofChar (G.cOf ν (σ a)) (hc (σ a)) := funext hσ
  obtain rfl : h = n := by simpa using Fintype.card_congr σ
  let φ := multiProdEquiv e fun a =>
    (GlobalTheory.LocGL.equivRep (IrrRep.det (Fin 1) (G.cOf ν (σ a)) (hc (σ a)))).symm
  have h1 : IsSubquotient π (multiProd e fun a => detRep (Fin 1) (G.cOf ν (σ a))) :=
    he.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have h2 := h1.trans (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e fun a => G.cOf ν (σ a))
  exact hOrd hLit V π hπs hπi (G.cOf ν) hc σ h2
end UpperTheory.TNZ.Grp
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TNZ.Grp
theorem step_suppProd_alt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (G : Grp k n) : G.Step_suppProd_alt :=
  _root_.UpperTheory.TNZ.Grp.step_spTop_alt G UpperTheory.TNZ.step_spLat (step_spUniq G) (_root_.UpperTheory.TNZ.Grp.step_spCount_alt G) (step_spLift G) (step_spTwBasic G) (step_spRes G)
    (step_spPiEta G) _root_.UpperTheory.TNZ.Grp.step_spOrd_alt (_root_.UpperTheory.TNZ.Grp.step_spPiSub_alt G) (_root_.UpperTheory.TNZ.Grp.step_spSupp_alt G) _root_.UpperTheory.TNZ.step_cuspSupp_alt _root_.UpperTheory.TNZ.step_prodIrr_alt
    UpperTheory.TNZ.step_tensorVec
end UpperTheory.TNZ.Grp
end
end
