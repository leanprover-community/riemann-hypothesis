import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAtOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExpansionIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
import Development.AutomorphicArithmetic.LocalEmbeddings.StairDepth

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

theorem nsmul_mem_of_mem_halfCoset {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {r x : Mx D m n}
    (hr : K • r ∈ Λ) (h : x ∈ halfCoset e Λ K r) : K • x ∈ Λ := by
  obtain ⟨u, hu, -, rfl⟩ := h
  rw [nsmul_add]
  exact add_mem hr (nsmul_mem (nsmul_mem hu K) K)

theorem eq_of_mem_halfCoset_reps {D : D7} {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {K : ℕ} {R : Finset (Mx D m n)}
    (hR3 : ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e Λ K r → r = r') {r r₀ x : Mx D m n} (hr : r ∈ R) (hr₀ : r₀ ∈ R)
    (hm : x ∈ halfCoset e Λ K r) (hm₀ : x ∈ halfCoset e Λ K r₀) : r = r₀ := by
  refine hR3 r hr r₀ hr₀ ?_
  rw [← halfCoset_eq hm, halfCoset_eq hm₀]
  exact mem_halfCoset_self _ _ _ _

theorem exists_cosetExpansion_of_depthOK : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  classical
  intro D T L sc G W U μ₀ hL S t Φ β e τ K hK he hexp hdep
  by_cases hτ : τ = 0
  · subst hτ
    exact ⟨0, hK, ⟨e, he, hexp⟩, fun d hd => by simp at hd⟩
  obtain ⟨d₀, hd₀⟩ := Finsupp.support_nonempty_iff.2 hτ
  have hP0 := hexp.1 d₀ hd₀
  have hR1 : ∀ j : Fin D.R.m, ∃ R : Finset (WO (G.pS (.top t j)) (G.pT (.top t j))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.top t j)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.top t j) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.top t j)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.top t j)) K r → r = r' := fun j =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t j j.2).1.1.fg
      (isLattice_pairs G hL t j j.2).1.2.fg _ (K * K) (Nat.mul_pos hK hK))
  have hR2 : ∀ i : Fin D.R.m, ∃ R : Finset (WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ r ∈ R, IsHalf e r ∧ K • r ∈ pairLat G (.chi i D.R.m)) ∧
      (∀ x, IsHalf e x → K • x ∈ pairLat G (.chi i D.R.m) → ∃ r ∈ R, x ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r) ∧
      ∀ r ∈ R, ∀ r' ∈ R, r' ∈ halfCoset e (pairLat G (.chi i D.R.m)) K r → r = r' := fun i =>
    exists_halfCoset_reps e hK (GlobalTheory.LatFinMod.latO_finite_mod D _ _ _ _ (isLattice_pairs G hL t i i.2).2.1.fg
      (isLattice_pairs G hL t i i.2).2.2.fg _ (K * K) (Nat.mul_pos hK hK))
  choose R1 hR1 using hR1
  choose R2 hR2 using hR2
  let dat : (∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j))) →
      (∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) → PureDat G t :=
    fun ρ ρ' => ((fun j => cosetDatum (d₀.1 j) K (ρ j)), fun i => cosetDatum (d₀.2 i) K (ρ' i))
  set τ' : PureDat G t →₀ ℂ := ∑ ρ ∈ Fintype.piFinset R1, ∑ ρ' ∈ Fintype.piFinset R2,
      Finsupp.single (dat ρ ρ') (flatProd S t Φ β ρ ρ') with hτ'
  have hsupp : ∀ d' ∈ τ'.support, ∃ ρ ∈ Fintype.piFinset R1, ∃ ρ' ∈ Fintype.piFinset R2, d' = dat ρ ρ' := by
    intro d' hd'
    rw [hτ'] at hd'
    obtain ⟨ρ, hρ, h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hd')
    obtain ⟨ρ', hρ', h3⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum h2)
    exact ⟨ρ, hρ, ρ', hρ', Finset.mem_singleton.1 (Finsupp.support_single_subset h3)⟩
  refine ⟨τ', hK, ⟨e, he, fun d' hd' => ?_, fun x y hx hy => ?_⟩, fun d' hd' => ?_⟩
  · obtain ⟨ρ, -, ρ', -, rfl⟩ := hsupp d' hd'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · obtain ⟨a, b, c⟩ := hP0.1 j
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
    · obtain ⟨a, b, c⟩ := hP0.2 i
      exact ⟨(cosetDatum_P _ _ _).trans a, (cosetDatum_e _ _ _).trans b, (cosetIndicatorFinDatum_point _ _ _).trans c⟩
  · let g : PureDat G t → ℂ → ℂ := fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)
    have h0 : ∀ d, g d 0 = 0 := fun d => by simp [g]
    have hadd : ∀ d b₁ b₂, g d (b₁ + b₂) = g d b₁ + g d b₂ := fun d b₁ b₂ => by simp only [g]; ring
    change Finsupp.sum τ' g = _
    rw [hτ', ← Finsupp.sum_finsetSum_index h0 hadd]
    simp_rw [← Finsupp.sum_finsetSum_index h0 hadd, Finsupp.sum_single_index (h0 _)]
    have hfn1 : ∀ ρ ∈ Fintype.piFinset R1, ∀ j, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j) =
        (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) := fun ρ hρ j =>
      congrFun (cosetDatum_fn (d₀.1 j) (hP0.1 j).2.1 hK ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).1
        ((hR1 j).1 _ (Fintype.mem_piFinset.1 hρ j)).2) (x j)
    have hfn2 : ∀ ρ' ∈ Fintype.piFinset R2, ∀ i, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ' hρ' i =>
      congrFun (cosetDatum_fn (d₀.2 i) (hP0.2 i).2.1 hK ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).1
        ((hR2 i).1 _ (Fintype.mem_piFinset.1 hρ' i)).2) (y i)
    simp only [g, dat]
    have hsum : ∀ ρ ∈ Fintype.piFinset R1, ∀ ρ' ∈ Fintype.piFinset R2,
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (cosetDatum (d₀.1 j) K (ρ j)).fn (x j)) * ∏ i : Fin D.R.m, (cosetDatum (d₀.2 i) K (ρ' i)).fn (y i) =
        flatProd S t Φ β ρ ρ' * (∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j)) *
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) := fun ρ hρ ρ' hρ' => by
      rw [Finset.prod_congr rfl fun j _ => hfn1 ρ hρ j, Finset.prod_congr rfl fun i _ => hfn2 ρ' hρ' i]
    rw [Finset.sum_congr rfl fun ρ hρ => Finset.sum_congr rfl fun ρ' hρ' => hsum ρ hρ ρ' hρ']
    show _ = flatProd S t Φ β x y
    by_cases hin : (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)
    · have h1 := fun j => (hR1 j).2.1 (x j) (hx j) (hin.1 j)
      have h2 := fun i => (hR2 i).2.1 (y i) (hy i) (hin.2 i)
      choose ρ0 hρ0 hxρ0 using h1
      choose ρ0' hρ0' hyρ0' using h2
      have hmem : ρ0 ∈ Fintype.piFinset R1 := Fintype.mem_piFinset.2 hρ0
      have hmem' : ρ0' ∈ Fintype.piFinset R2 := Fintype.mem_piFinset.2 hρ0'
      have hz1 : ∀ ρ ∈ Fintype.piFinset R1, ρ ≠ ρ0 →
          ∏ j : Fin D.R.m, (halfCoset e (pairLat G (.top t j)) K (ρ j)).indicator 1 (x j) = (0 : ℂ) := by
        intro ρ hρ hne
        obtain ⟨j, hj⟩ : ∃ j, ρ j ≠ ρ0 j := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem (fun hm => hj ?_) _)
        exact eq_of_mem_halfCoset_reps (hR1 j).2.2 (Fintype.mem_piFinset.1 hρ j) (hρ0 j) hm (hxρ0 j)
      have hz2 : ∀ ρ' ∈ Fintype.piFinset R2, ρ' ≠ ρ0' →
          ∏ i : Fin D.R.m, (halfCoset e (pairLat G (.chi i D.R.m)) K (ρ' i)).indicator 1 (y i) = (0 : ℂ) := by
        intro ρ' hρ' hne
        obtain ⟨i, hi⟩ : ∃ i, ρ' i ≠ ρ0' i := by
          by_contra hc
          push_neg at hc
          exact hne (funext hc)
        refine Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem (fun hm => hi ?_) _)
        exact eq_of_mem_halfCoset_reps (hR2 i).2.2 (Fintype.mem_piFinset.1 hρ' i) (hρ0' i) hm (hyρ0' i)
      rw [Finset.sum_eq_single_of_mem ρ0 hmem ?s1, Finset.sum_eq_single_of_mem ρ0' hmem' ?s2]
      case s1 =>
        intro ρ hρ hne
        exact Finset.sum_eq_zero fun ρ' _ => mul_eq_zero_of_left (mul_eq_zero_of_right _ (hz1 ρ hρ hne)) _
      case s2 =>
        intro ρ' hρ' hne
        exact mul_eq_zero_of_right _ (hz2 ρ' hρ' hne)
      refine (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (Finset.prod_eq_one fun j _ => ?_))
        (Finset.prod_eq_one fun i _ => ?_)).trans ?_
      · exact Set.indicator_of_mem (hxρ0 j) _
      · exact Set.indicator_of_mem (hyρ0' i) _
      rw [mul_one, mul_one]
      choose u hu hu' hxu using hxρ0
      choose v hv hv' hyv using hyρ0'
      have hx' : x = ρ0 + K • u := funext fun j => by rw [Pi.add_apply, Pi.smul_apply]; exact hxu j
      have hy' : y = ρ0' + K • v := funext fun i => by rw [Pi.add_apply, Pi.smul_apply]; exact hyv i
      rw [hx', hy']
      exact (hdep.2 ρ0 u ρ0' v (fun j => ((hR1 j).1 _ (hρ0 j)).1) (fun i => ((hR2 i).1 _ (hρ0' i)).1)
        (fun j => ⟨hu' j, hu j⟩) (fun i => ⟨hv' i, hv i⟩)).symm
    · have hzero : flatProd S t Φ β x y = 0 := by
        by_contra h
        exact hin (hdep.1 x y hx hy h)
      rw [hzero]
      refine Finset.sum_eq_zero fun ρ hρ => Finset.sum_eq_zero fun ρ' hρ' => ?_
      rw [Fintype.mem_piFinset] at hρ hρ'
      rcases not_and_or.1 hin with h | h
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        exact mul_eq_zero_of_left (mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem
          (fun hm => hj (nsmul_mem_of_mem_halfCoset ((hR1 j).1 _ (hρ j)).2 hm)) _))) _
      · push_neg at h
        obtain ⟨i, hi⟩ := h
        exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem
          (fun hm => hi (nsmul_mem_of_mem_halfCoset ((hR2 i).1 _ (hρ' i)).2 hm)) _))
  · obtain ⟨ρ, hρ, ρ', hρ', rfl⟩ := hsupp d' hd'
    rw [Fintype.mem_piFinset] at hρ hρ'
    refine ⟨fun j => ?_, fun i => ?_⟩
    · have h := (hR1 j).1 _ (hρ j)
      exact isCosetDatum_cosetDatum _ hK ((hP0.1 j).2.1 ▸ h.1) h.2
    · have h := (hR2 i).1 _ (hρ' i)
      exact isCosetDatum_cosetDatum _ hK ((hP0.2 i).2.1 ▸ h.1) h.2

end GlobalTheory.DepthUnf

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} {μ₀ : T}, L.Is μ₀ → ∀ (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) (K : ℕ), 0 < K → IsIdemSum e (locPl G t) → ExpWith S t Φ β e τ → DepthOK S t Φ β e K → ∃ τ', IsCosetExpansion S t Φ β K τ' := by
  atlas_forward_decl GlobalTheory.DepthUnf.exists_cosetExpansion_of_depthOK
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem nsmul_mem_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {x : WO (G.pS p) (G.pT p)} (hx : d.fn x ≠ 0) : k • x ∈ pairLat G p := by
  obtain ⟨x₀, -, h1, hfn⟩ := h
  rw [hfn] at hx
  obtain ⟨u, hu, -, rfl⟩ := Set.mem_of_indicator_ne_zero hx
  rw [nsmul_add]
  exact add_mem h1 (nsmul_mem (nsmul_mem hu k) k)

theorem fn_add_nsmul_of_isCosetDatum {t : T} {p : Pair T} {k : ℕ} {d : FinDatum G t p} (h : IsCosetDatum k d)
    {u : WO (G.pS p) (G.pT p)} (hu : u ∈ pairLat G p) (hu' : IsHalf d.e u) (x : WO (G.pS p) (G.pT p)) :
    d.fn (x + k • u) = d.fn x := by
  obtain ⟨x₀, -, -, hfn⟩ := h
  rw [hfn]
  by_cases hx : x ∈ halfCoset d.e (pairLat G p) k x₀
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((add_nsmul_mem_halfCoset_iff hu hu').2 hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (add_nsmul_mem_halfCoset_iff hu hu').1 hx)]

theorem depthOK_of_isCosetExpansion : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) (τ : PureDat G t →₀ ℂ), IsCosetExpansion S t Φ β k τ → ∃ e, IsIdemSum e (locPl G t) ∧ ExpWith S t Φ β e τ ∧ DepthOK S t Φ β e k := by
  intro D T L sc G W U S t Φ β k τ h
  obtain ⟨-, ⟨e, he, hP, hsum⟩, hcos⟩ := h
  refine ⟨e, he, ⟨hP, hsum⟩, ?_, ?_⟩
  · intro x y hx hy hne
    unfold flatProd at hne
    rw [← hsum x y hx hy] at hne
    obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    beta_reduce at hne
    have h1 : ∏ j, (d.1 j).fn (x j) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero, zero_mul])
    have h2 : ∏ i, (d.2 i).fn (y i) ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    rw [Finset.prod_ne_zero_iff] at h1 h2
    exact ⟨fun j => nsmul_mem_of_isCosetDatum ((hcos d hd).1 j) (h1 j (Finset.mem_univ _)),
      fun i => nsmul_mem_of_isCosetDatum ((hcos d hd).2 i) (h2 i (Finset.mem_univ _))⟩
  · intro x u y v hx hy hu hv
    have hx' : ∀ j, IsHalf e ((x + k • u) j) := fun j a b => by
      show e * (x j + k • u j) a b = (x j + k • u j) a b
      rw [Matrix.add_apply, mul_add, hx j a b, isHalf_nsmul_of k (hu j).1 a b]
    have hy' : ∀ i, IsHalf e ((y + k • v) i) := fun i a b => by
      show e * (y i + k • v i) a b = (y i + k • v i) a b
      rw [Matrix.add_apply, mul_add, hy i a b, isHalf_nsmul_of k (hv i).1 a b]
    unfold flatProd
    rw [← hsum _ _ hx' hy', ← hsum x y hx hy]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hx1 : ∀ j, (d.1 j).fn ((x + k • u) j) = (d.1 j).fn (x j) := fun j =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).1 j) (hu j).2 (((hP d hd).1 j).2.1 ▸ (hu j).1) (x j)
    have hy1 : ∀ i, (d.2 i).fn ((y + k • v) i) = (d.2 i).fn (y i) := fun i =>
      fn_add_nsmul_of_isCosetDatum ((hcos d hd).2 i) (hv i).2 (((hP d hd).2 i).2.1 ▸ (hv i).1) (y i)
    simp only [hx1, hy1]

end GlobalTheory.DepthUnf

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthPeriodic_of_cosetIndicatorExpansion : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) (τ : PureDat G t →₀ ℂ), IsCosetExpansion S t Φ β k τ → ∃ e, IsIdemSum e (locPl G t) ∧ ExpWith S t Φ β e τ ∧ DepthOK S t Φ β e k := by
  atlas_forward_decl GlobalTheory.DepthUnf.depthOK_of_isCosetExpansion
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DepthUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem gcd_nsmul_mem_of {A S : Type*} [AddCommGroup A] [SetLike S A] [AddSubgroupClass S A] (Λ : S) {x : A}
    {k k' : ℕ} (h : k • x ∈ Λ) (h' : k' • x ∈ Λ) : Nat.gcd k k' • x ∈ Λ := by
  have e : Nat.gcd k k' • x = Nat.gcdA k k' • (k • x) + Nat.gcdB k k' • (k' • x) := by
    rw [← natCast_zsmul, ← natCast_zsmul, ← natCast_zsmul, smul_smul, smul_smul, ← add_smul, Nat.gcd_eq_gcd_ab]
    congr 1; ring
  rw [e]
  exact add_mem (zsmul_mem h _) (zsmul_mem h' _)

theorem add_mul_succ_zsmul {A : Type*} [AddCommGroup A] (k : ℕ) (n : ℤ) (z w : A) :
    z + ((k : ℤ) * (n + 1)) • w = (z + ((k : ℤ) * n) • w) + k • w := by
  rw [mul_add, mul_one, add_smul, natCast_zsmul, add_assoc]

theorem add_mul_pred_zsmul {A : Type*} [AddCommGroup A] (k : ℕ) (n : ℤ) (z w : A) :
    (z + ((k : ℤ) * (n - 1)) • w) + k • w = z + ((k : ℤ) * n) • w := by
  rw [add_assoc, ← natCast_zsmul, ← add_smul]; congr 2; ring

theorem add_gcd_nsmul_eq {A : Type*} [AddCommGroup A] (k k' : ℕ) (z w : A) :
    z + Nat.gcd k k' • w = (z + ((k : ℤ) * Nat.gcdA k k') • w) + ((k' : ℤ) * Nat.gcdB k k') • w := by
  rw [add_assoc, ← add_smul, ← Nat.gcd_eq_gcd_ab, natCast_zsmul]

theorem isHalf_add_zsmul {e : AE D} {m n : ℕ} {a b : Mx D m n} (ha : IsHalf e a) (hb : IsHalf e b) (c : ℤ) :
    IsHalf e (a + c • b) := fun i j => by
  have h1 := ha i j
  have h2 := hb i j
  show e * (a i j + c • b i j) = a i j + c • b i j
  rw [zsmul_eq_mul, mul_add, mul_left_comm, h1, h2]

theorem DepthOK.flatProd_add_zsmul {S : GridChoice W U} {t : T} {Φ : G.Datum} {β : CosFam G t} {e : AE D} {k : ℕ}
    (hK : DepthOK S t Φ β e k) (c : ℤ)
    (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))
    (hx : ∀ j, IsHalf e (x j)) (hy : ∀ i, IsHalf e (y i))
    (hu : ∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j))
    (hv : ∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) :
    flatProd S t Φ β (x + ((k : ℤ) * c) • u) (y + ((k : ℤ) * c) • v) = flatProd S t Φ β x y := by
  induction c using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [add_mul_succ_zsmul, add_mul_succ_zsmul,
      hK.2 (x + ((k : ℤ) * n) • u) u (y + ((k : ℤ) * n) • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _) (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv, ih]
  | pred n ih =>
    rw [← hK.2 (x + ((k : ℤ) * (-n - 1)) • u) u (y + ((k : ℤ) * (-n - 1)) • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _) (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv,
      add_mul_pred_zsmul, add_mul_pred_zsmul, ih]

theorem depthOK_gcd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (k k' : ℕ)
    (h : DepthOK S t Φ β e k) (h' : DepthOK S t Φ β e k') : DepthOK S t Φ β e (Nat.gcd k k') := by
  refine ⟨fun x y hx hy hF => ⟨fun j => gcd_nsmul_mem_of _ ((h.1 x y hx hy hF).1 j) ((h'.1 x y hx hy hF).1 j),
    fun i => gcd_nsmul_mem_of _ ((h.1 x y hx hy hF).2 i) ((h'.1 x y hx hy hF).2 i)⟩, ?_⟩
  intro x u y v hx hy hu hv
  rw [add_gcd_nsmul_eq k k' x u, add_gcd_nsmul_eq k k' y v,
    h'.flatProd_add_zsmul _ (x + ((k : ℤ) * Nat.gcdA k k') • u) u (y + ((k : ℤ) * Nat.gcdA k k') • v) v (fun j => isHalf_add_zsmul (hx j) (hu j).1 _)
      (fun i => isHalf_add_zsmul (hy i) (hv i).1 _) hu hv,
    h.flatProd_add_zsmul _ x u y v hx hy hu hv]

end GlobalTheory.DepthUnf

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatProductDepthPeriodic_gcd : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (k k' : ℕ), DepthOK S t Φ β e k → DepthOK S t Φ β e k' → DepthOK S t Φ β e (Nat.gcd k k') := by
  atlas_forward_decl GlobalTheory.DepthUnf.depthOK_gcd
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

private theorem val_nat_le_unif (w : Pl D.host.E) {p : ℕ} (hp : (p : 𝓞 D.host.E) ∈ w.asIdeal) :
    valuation (Kw w) (p : Kw w) ≤ valuation (Kw w) (unifAt w : Kw w) := by
  rw [isUnif_unifAt w]
  refine le_uniformizer_iff.2 ((Comparison₂.vEq w).lt_one_iff_lt_one.2 ?_)
  rw [← map_natCast (algebraMap D.host.E (Kw w)), Good.valued_alg, ← map_natCast (algebraMap (𝓞 D.host.E) D.host.E)]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hp

private theorem exists_depth (P : Finset (Pl D.host.E)) (n : Pl D.host.E → ℕ) : ∃ K : ℕ, 0 < K ∧
    (∀ l B : ℕ, l.Prime → (∀ w ∈ P, (l : 𝓞 D.host.E) ∈ w.asIdeal → n w ≤ B) → padicValNat l K ≤ B) ∧
    ∀ w ∈ P, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w) := by
  classical
  let N : ℕ → ℕ := fun p => (P.filter fun w => Formalism.EigenvalueLevelCeiling.plc w = p).sup n
  have hpr : ∀ p ∈ P.image Formalism.EigenvalueLevelCeiling.plc, p.Prime := fun p hp => by
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hp
    exact Formalism.EigenvalueLevelCeiling.plc_prime w
  refine ⟨∏ p ∈ P.image Formalism.EigenvalueLevelCeiling.plc, p ^ N p, Finset.prod_pos fun p hp => pow_pos (hpr p hp).pos _, fun l B hl hB => ?_,
    fun w hw => ?_⟩
  · have hN : N l ≤ B := Finset.sup_le fun w hw => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hw
      exact hB w h1 (h2 ▸ Formalism.EigenvalueLevelCeiling.plc_mem w)
    rw [← Nat.factorization_def _ hl, Nat.factorization_prod fun p hp => pow_ne_zero _ (hpr p hp).ne_zero,
      Finset.sum_congr rfl fun p hp => (hpr p hp).factorization_pow, Finset.sum_apply']
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs
    · exact hN
    · exact Nat.zero_le _
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p => p ^ N p) (Finset.mem_image_of_mem Formalism.EigenvalueLevelCeiling.plc hw)
    have hn : n w ≤ N (Formalism.EigenvalueLevelCeiling.plc w) := Finset.le_sup (f := n) (Finset.mem_filter.2 ⟨hw, rfl⟩)
    have hc1 : valuation (Kw w) (c : Kw w) ≤ 1 := (Valuation.mem_integer_iff _ _).1 (natCast_mem _ c)
    rw [hc, Nat.cast_mul, map_mul]
    refine (mul_le_mul' ?_ hc1).trans ((mul_one _).le.trans (val_pow_anti (isUnif_unifAt w) hn))
    rw [Nat.cast_pow, Units.val_pow_eq_pow_val, map_pow, map_pow]
    exact pow_le_pow_left' (val_nat_le_unif w (Formalism.EigenvalueLevelCeiling.plc_mem w)) _

private theorem frAt_nsmul (w : Pl D.host.E) {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (K : ℕ)
    (x : Mx D b a) (r : Fin b) (s : Fin a) : frAt w β' β (K • x) r s = (K : Kw w) * frAt w β' β x r s := by
  induction K with
  | zero => simp [frAt, Comparison₂.fr]
  | succ K ih => rw [succ_nsmul, frAt_add, Matrix.add_apply, ih, Nat.cast_succ, add_mul, one_mul]

section Lat

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
  {P : Finset (Pl D.host.E)} {n : Pl D.host.E → ℕ} {K : ℕ}

private theorem nsmul_mem_lat (hS : IsSelfDualC S ΛS) (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {e : AE D} (he : IsIdemSum e P)
    (hAA : ∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)
    (hK : ∀ w ∈ P, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w)) {x : WO S T}
    (hx : IsHalf e x)
    (h : ∀ w ∈ P, ∀ r s, valuation (Kw w) (frAt w βT βS x r s) ≤ valuation (Kw w) (((unifAt w ^ n w)⁻¹ : (Kw w)ˣ) : Kw w)) :
    K • x ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True := by
  have hx' : IsHalf e (K • x) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hx i j]
  refine GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hS he hAA hx' (GlobalTheory.RowLatChi.mem_hatMx_of_int hβS hβT he hx' fun w hw r s => ?_)
  refine (Comparison₂.vEq w).le_one_iff_le_one.1 ?_
  change valuation (Kw w) (frAt w βT βS (K • x) r s) ≤ 1
  rw [frAt_nsmul, map_mul]
  refine (mul_le_mul' (hK w hw) (h w hw r s)).trans_eq ?_
  rw [← map_mul, Units.mul_inv, map_one]

private theorem nsmul_small (hS : IsSelfDualC S ΛS) (hβS : IsFrame βS ΛS) (hβT : IsFrame βT ΛT) {w : Pl D.host.E}
    (hAA : ∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) {c : ValueGroupWithZero (Kw w)}
    (hK : valuation (Kw w) (K : Kw w) ≤ c) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (r : Fin T.rank) (s : Fin S.rank) :
    valuation (Kw w) (frAt w βT βS (K • u) r s) ≤ c := by
  have h1 : valuation (Kw w) (frAt w βT βS u r s) ≤ 1 :=
    (Comparison₂.vEq w).le_one_iff_le_one.2 (GlobalTheory.RowLatChi.int_of_mem_latO hS hβS hβT w hAA hu r s)
  rw [frAt_nsmul, map_mul]
  exact (mul_le_mul' hK h1).trans_eq (mul_one _)

end Lat

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

private theorem isSBArgs_of_mem_good_places {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    IsSBArgs (locGrid G t P) (unifAt P) (depthAt G P) (S.term t Φ β ⟨P, hl⟩).datum := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ G.pl.S0, G.pl.w v = P := by simpa [Places.W0] using hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT ⊢
  have hKO : ∀ j, 0 < j → j < (locGrid G t P).m → givenLevel G t P ((locGrid G t P).m, j) = KO (Kw P) _ := by
    intro j hj _
    have key : ∀ i, 0 < i → givenLevel G t P (i, j) = KO _ _ := by
      rintro (_ | i) hi
      · omega
      · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        rfl
    exact key _ hm
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT hKO
  have hb := hβ ⟨P, hl⟩
  have hb' : β ⟨P, hl⟩ ∈ unfSupport (psiAt W P) (unitVol P) false
      (Reps.through hs (givenLevel G t P) (stair (locGrid G t P) (unifAt P) (cosExp G P))) (Tflip W S.B t Φ P) := by
    have : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
    rw [this] at hb
    exact hb
  have hβ' := funext (hO _ hb')
  have h := GlobalTheory.StairDepth.isSBArgs_stair hs (psiAt W P) (unitVol P) hm2 (isUnif_unifAt P) h00.cond hT (keepAt G P)
  rw [← GlobalTheory.StairDepth.elt_eq hs (givenLevel G t P) _ _ hm2, ← hβ'] at h
  exact h

private theorem depthOK_of {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (β : CosFam G t)
    {n : Pl D.host.E → ℕ} (hF : ∀ w : locPl G t, IsSBArgs (locGrid G t w.1) (unifAt w.1) (n w.1) (S.term t Φ β w).datum)
    {K : ℕ} (hK : ∀ w ∈ locPl G t, valuation (Kw w) (K : Kw w) ≤ valuation (Kw w) ((unifAt w ^ n w : (Kw w)ˣ) : Kw w))
    {e : AE D} (he : IsIdemSum e (locPl G t)) : DepthOK S t Φ β e K := by
  have hAA : ∀ w ∈ locPl G t, (∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1 := by
    intro w hw
    have hb := Good.badInt_notMem hL hde hc hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [Good.valued_alg]
      exact Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [Good.valued_alg]
      exact Good.valuation_nat hN
  have sT : ∀ j : Fin D.R.m, IsSelfDualC (G.pS (.top t j)) (G.latS (.top t j)) := fun j =>
    (G.isV (X := .top j) j.2.le fun _ e => by cases e).sd
  have sC : ∀ i : Fin D.R.m, IsSelfDualC (G.pS (.chi i D.R.m : Pair T)) (G.latS (.chi i D.R.m : Pair T)) := fun i =>
    isSelfDualC_neg (G.isV (X := .grid (i + 1) D.R.m) ⟨i.2, le_rfl⟩ fun j e => by injection e with h1; omega).sd
  refine ⟨fun x y hx hy hne => ?_, fun x u y v _ _ hu hv => ?_⟩
  · have hw : ∀ w : locPl G t, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y) ≠ 0 := fun w h0 =>
      hne (Finset.prod_eq_zero (Finset.mem_univ w) h0)
    refine ⟨fun j => nsmul_mem_lat (sT j) (S.βp_is j j.2.le) (S.βp_is (j + 1) j.2) he (fun w hw => (hAA w hw).2) hK (hx j)
        fun w hwP r s => ?_,
      fun i => nsmul_mem_lat (sC i) (S.B.isFrame_β hL i.2 le_rfl) (S.B.isFrame_β hL i.2.le le_rfl) he
        (fun w hw => (hAA w hw).2) hK (hy i) fun w hwP r s => ?_⟩
    · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).1 j j.2 (Fin.cast (topRank_eq G t w j.2).symm r)
        (Fin.cast (topRank_eq G t w j.2.le).symm s)
      rw [colAt_eq S t w x j.2] at this
      exact this
    · have := ((hF ⟨w, hwP⟩).supp _ _ (hw ⟨w, hwP⟩)).2 i i.2
        (Fin.cast (rank_vertex G t w (X := (i, D.R.m)) ⟨i.2.le, le_rfl⟩).symm r)
        (Fin.cast (rank_vertex G t w (X := (i + 1, D.R.m)) ⟨i.2, le_rfl⟩).symm s)
      rw [rowAt_eq S t w y i.2] at this
      exact this
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [colAt_add, rowAt_add]
    refine (hF w).per _ _ _ _ (fun j hj r s => ?_) (fun i hi r s => ?_)
    · rw [colAt_eq S t w _ hj]
      exact nsmul_small (sT ⟨j, hj⟩) (S.βp_is j hj.le) (S.βp_is (j + 1) hj) (hAA w.1 w.2).1 (hK w.1 w.2) (hu ⟨j, hj⟩).2 _ _
    · rw [rowAt_eq S t w _ hi]
      exact nsmul_small (sC ⟨i, hi⟩) (S.B.isFrame_β hL hi le_rfl) (S.B.isFrame_β hL hi.le le_rfl) (hAA w.1 w.2).1
        (hK w.1 w.2) (hv ⟨i, hi⟩).2 _ _

private theorem depth_main {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {β : CosFam G t} (hβ : β ∈ S.supp t Φ) :
    ∃ K : ℕ, 0 < K ∧ (∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away G t w →
      padicValNat l K ≤ depL G l) ∧ ∀ e, IsIdemSum e (locPl G t) → DepthOK S t Φ β e K := by
  classical
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hSB : ∀ w : Pl D.host.E, ∃ n, (w ∈ G.pl.W0 → n = depthAt G w) ∧ ∀ hw : w ∈ locPl G t,
      IsSBArgs (locGrid G t w) (unifAt w) n (S.term t Φ β ⟨w, hw⟩).datum := fun w => by
    by_cases h0 : w ∈ G.pl.W0
    · exact ⟨_, fun _ => rfl, fun hw => isSBArgs_of_mem_good_places hL S t Φ hde hc h0 hw hβ⟩
    by_cases hw : w ∈ locPl G t
    · have hg := (Good.locGrid_isGood hL G W t hde hc).1 w hw
      have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
      haveI := (isUnitVol_unitVol w).1
      obtain ⟨n, hn⟩ := exists_isSBArgs_flat (locGrid G t w) one_le_sLen (psiAt W w) (unitVol w) (unifAt w) (depthAt G w)
        (Tflip W S.B t Φ w) (keepAt G w) ((repsAt G t w).elt (β ⟨w, hw⟩)) hm h00.unif h00.cond
        (isTensor_Tflip hL W S.B t Φ hde hc hw)
      exact ⟨n, fun h => absurd h h0, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h h0, fun h => absurd h hw⟩
  choose n hn0 hn using hSB
  obtain ⟨K, hK0, hKl, hK⟩ := exists_depth (locPl G t) n
  refine ⟨K, hK0, fun w l hl hlw hA => hKl l _ hl fun P hP hlP => ?_,
    fun e he => depthOK_of hL S t Φ hde hc β (fun w => hn w.1 w.2) hK he⟩
  have hW : P ∈ G.pl.W0 := by
    rcases Good.locPl_cases hP with ⟨a, b⟩ | ⟨a, -, b⟩
    · rw [b]
      unfold Places.W0
      convert Finset.mem_image_of_mem _ a
    · exact absurd hlw ((hA P b).resolve_left a l hl hlP)
  rw [hn0 P hW]
  exact Finset.le_sup (f := depthAt G) (Finset.mem_filter.2 ⟨hW, hlP⟩)

end SlopeTestRemainingChoices

theorem _root_.GlobalTheory.T.flatTensor_depth_conditions_away_from_twist : BigC fun {D} _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ∀ (t : _) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∃ K : ℕ, 0 < K ∧ (∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w → padicValNat l K ≤ depL ch.G l) ∧ ∀ e, IsIdemSum e (locPl ch.G t) → DepthOK ch.S.toGridChoice t Φ β e K := by
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ t Φ β hβ => ?_⟩⟩⟩
  exact depth_main hS.core.lev ch.S.toGridChoice t Φ (GlobalTheory.RowClaim.Test.pde_ne_q hS) (GlobalTheory.RowClaim.Test.guard hS t) hβ
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.DepthUnf GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.DepthUnf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem depthK_of_sumOKK₂ : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → DepthK := by
  intro _ _
  obtain ⟨CF0, h4⟩ := GlobalTheory.T.flatTensor_depth_conditions_away_from_twist
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h4⟩ := h4 CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x₀, h4⟩ := h4 ε C hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hi hsc hf => ?_⟩
  have H := h4 D large₂ he hx Γ Pl0 T A Ks R F hS ch hi hsc hf
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := GlobalTheory.RowClaim.Test.pde_ne_q hS
  intro t Φ β hβ
  have hc : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := GlobalTheory.RowClaim.Test.guard hS t
  obtain ⟨K, hK, hval, hdep⟩ := H t Φ β hβ
  obtain ⟨τ, e, he, hexp⟩ := GridChoice.sumOK_ex hL ch.S.toGridChoice t Φ hde hc β hβ
  obtain ⟨τK, hτK⟩ := GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic hL ch.S.toGridChoice t Φ β e τ K hK he hexp (hdep e he)
  obtain ⟨τm, hτm⟩ := hτK.exists_expDepth
  refine ⟨⟨τm, hτm⟩, fun w l hl hlw haw => ?_⟩
  have hk : 0 < expDepth ch.S.toGridChoice t Φ β := hτm.1
  obtain ⟨e', he', hexp', hdk⟩ := GlobalTheory.T.depthPeriodic_of_cosetIndicatorExpansion _ t Φ β _ τm hτm
  have hg := GlobalTheory.T.flatProductDepthPeriodic_gcd _ t Φ β e' _ _ hdk (hdep e' he')
  obtain ⟨τg, hτg⟩ := GlobalTheory.T.exists_cosetIndicatorExpansion_of_depthPeriodic hL _ t Φ β e' τm _ (Nat.gcd_pos_of_pos_left _ hk) he' hexp' hg
  have hle : expDepth ch.S.toGridChoice t Φ β ≤ Nat.gcd (expDepth ch.S.toGridChoice t Φ β) K := Nat.sInf_le ⟨τg, hτg⟩
  have heq := le_antisymm (Nat.le_of_dvd hk (Nat.gcd_dvd_left _ _)) hle
  have hdvd : expDepth ch.S.toGridChoice t Φ β ∣ K := heq ▸ Nat.gcd_dvd_right _ K
  haveI := Fact.mk hl
  exact (padicValNat_dvd_iff_le hK.ne').1 ((pow_padicValNat_dvd).trans hdvd) |>.trans (hval w l hl hlw haw)

end GlobalTheory.DepthUnf

end
end
