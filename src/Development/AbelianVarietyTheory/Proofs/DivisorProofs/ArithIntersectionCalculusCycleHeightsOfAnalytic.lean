import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefined
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorSectionsNonvanishingFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductionIndependentOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalOfSymmetricMultiadditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaEveryPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjection

section
section
open Equiv

theorem GlobalTheory.perm_invariant_of_cons_swap :
  ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  intro α n F h1 h2
  let S : Subgroup (Equiv.Perm (Fin (n+2))) :=
    { carrier := {σ | ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L}
      mul_mem' := by
        intro σ τ hσ hτ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        have hτ' : ∀ L : Fin (n+2) → α, F (fun i => L (τ i)) = F L := hτ
        show ∀ L : Fin (n+2) → α, F (fun i => L ((σ * τ) i)) = F L
        intro L
        calc F (fun i => L ((σ * τ) i)) = F (fun i => L (σ (τ i))) := rfl
          _ = F (fun j => L (σ j)) := hτ' (fun j => L (σ j))
          _ = F L := hσ' L
      one_mem' := by
        show ∀ L : Fin (n+2) → α, F (fun i => L ((1 : Equiv.Perm (Fin (n+2))) i)) = F L
        intro L; rfl
      inv_mem' := by
        intro σ hσ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        show ∀ L : Fin (n+2) → α, F (fun i => L (σ⁻¹ i)) = F L
        intro L
        calc F (fun i => L (σ⁻¹ i)) = F (fun i => L (σ⁻¹ (σ i))) := (hσ' (fun j => L (σ⁻¹ j))).symm
          _ = F L := by simp }
  have memS : ∀ σ, σ ∈ S ↔ ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := fun σ => Iff.rfl
  have hfix : ∀ e : Equiv.Perm (Fin (n+1)), Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) ∈ S := by
    intro e
    rw [memS]
    intro L
    have hc : (fun i => L (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) i)) = Fin.cons (L 0) (fun i => Fin.tail L (e i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.tail]
    rw [hc, h1 (L 0) (Fin.tail L) e, Fin.cons_self_tail]
  have hswap : Equiv.swap (0 : Fin (n+2)) 1 ∈ S := by
    rw [memS]
    intro L
    have e1 : L = Fin.cons (L 0) (Fin.cons (L 1) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
    have e2 : (fun i => L (Equiv.swap (0 : Fin (n+2)) 1 i)) = Fin.cons (L 1) (Fin.cons (L 0) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · have a1 : (k.succ.succ : Fin (n+2)) ≠ 0 := Fin.succ_ne_zero _
          have a2 : (k.succ.succ : Fin (n+2)) ≠ 1 := by
            intro h
            rw [← Fin.succ_zero_eq_one] at h
            exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
          simp [Equiv.swap_apply_of_ne_of_ne a1 a2]
    rw [e2, ← h2 (L 0) (L 1)]
    exact congrArg F e1.symm
  have hp : ∀ p : Fin (n+2), Equiv.swap (0 : Fin (n+2)) p ∈ S := by
    intro p
    refine Fin.cases ?_ (fun k => ?_) p
    · rw [Equiv.swap_self]; exact S.one_mem
    · have h0 : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 0 = 0 := by simp
      have h1' : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 1 = k.succ := by
        rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ]
        simp
      have hc := Equiv.swap_apply_apply (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k)) 0 1
      rw [h0, h1'] at hc
      rw [hc]
      exact S.mul_mem (S.mul_mem (hfix _) hswap) (S.inv_mem (hfix _))
  have hdec : ∀ (p : Fin (n+2)) (e : Equiv.Perm (Fin (n+1))),
      Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) := by
    intro p e
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
  intro L e
  have he : e ∈ S := by
    rw [← Equiv.Perm.decomposeFin.symm_apply_apply e]
    rcases Equiv.Perm.decomposeFin e with ⟨p, e'⟩
    rw [hdec]
    exact S.mul_mem (hp p) (hfix e')
  exact (memS e).1 he L
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_invariant_of_cons_swap_and_tail : ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  atlas_forward_decl GlobalTheory.perm_invariant_of_cons_swap
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.VSwap

theorem finite_coheight_one_mem_supp {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [CompactSpace Z]
    (D : CartierDiv Z) : {z : Z | Order.coheight z = 1 ∧ z ∈ D.supp}.Finite := by
  classical
  have : IsNoetherian Z := {}
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible D.supp.isClosed
  refine (hS.image fun T => if h : IsIrreducible T then h.genericPoint else genericPoint Z).subset
    fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le hz.2)
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos (hi T hT)]
  have hg := (hi T hT).isGenericPoint_genericPoint (hc T hT)
  have h₁ : z ≤ (hi T hT).genericPoint := hg.specializes hzT
  have h₂ : (hi T hT).genericPoint < genericPoint Z := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Z := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hU.ge (Set.mem_sUnion.2 ⟨T, hT, hg.mem⟩))
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e => hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [hz.1] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

section

variable (hI : ArchInteg) (hR : ArchRecip) {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
  [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hq : IsAmb q) {e : ℕ} (hd : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
  {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (L : Fin e → HermLB q)

include hI hR hq hd hT in

theorem add_first (N M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    {u : A.B.ι → Y.functionFieldˣ} (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ}
    (ht : IsRatSec (M.tens A).B t) :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) (M.tens A) ht =
      recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr +
        recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) A hu := by
  have hp : IsRatSec (M.tens A).B (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) := PtHtComb.isRatSec_tens hr hu
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT (M.tens A) (Fin.cons N L) t ht _ hp]
  exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k Y q hq (e + 1) hd (T (e + 1) (Fin.cons N L)) (Fin.cons N L) M A r hr u hu _ hp
    fun _ _ _ _ => rfl

include hI hR hq hd hT in

theorem swap_of_sec (M N : HermLB q) (t : N.B.Sec) (ht : genericPoint Y ∈ nonzeroLocus t)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) {r' : N.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N.B r') :
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  have : IsNoetherian Y := hq.isNoetherian
  set S : Set Y := {genericPoint Y} ∪ {z | Order.coheight z = 1 ∧ z ∈ (divOfSec N.isLB t ht).supp} with hS
  have hfin : S.Finite := (Set.finite_singleton _).union (finite_coheight_one_mem_supp _)
  obtain ⟨B, s, v, hsS, hvS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq M S hfin
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS (Set.mem_union_left _ rfl)
  have hv : genericPoint Y ∈ nonzeroLocus v := hvS (Set.mem_union_left _ rfl)
  have hcov : ∀ z : Y, Order.coheight z = 1 → z ∉ nonzeroLocus t → z ∈ S := fun z hz hzt =>
    Set.mem_union_right _ ⟨hz, by_contra fun h => hzt ((notMem_supp_divOfSec (hL := N.isLB) (s := t) (hs := ht)).1 h)⟩
  have R1 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT (M.tens B) N L s t hs ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hsS (hcov z hz h))
  have R2 := GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections hR k Y q hq e hd T hT B N L v t hv ht fun z hz =>
    (em (z ∈ nonzeroLocus t)).elim Or.inr fun h => Or.inl (hvS (hcov z hz h))
  have A1 := add_first hI hR hq hd hT L N M B hr (isRatSec_ratOfSec v hv) (isRatSec_ratOfSec s hs)
  have A2 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT N (ratOfSec t ht) (isRatSec_ratOfSec t ht) M B L
  rw [GlobalTheory.T.mixedHeightInduction_independent_of_section hI hR k Y q hq e hd T hT N (Fin.cons M L) r' hr' _ (isRatSec_ratOfSec t ht)]
  linarith

end

theorem main : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T →
    ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r)
    (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'),
    recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr =
      recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  intro hI hR k _ Y _ _ q hq e hd T hT M N L r hr r' hr'
  obtain ⟨A, s, u, hsS, huS⟩ := GlobalTheory.T.exists_tensor_sections_nonvanishing_finite_set k Y q hq N {genericPoint Y} (Set.finite_singleton _)
  have hs : genericPoint Y ∈ nonzeroLocus s := hsS rfl
  have hu : genericPoint Y ∈ nonzeroLocus u := huS rfl
  have hp := PtHtComb.isRatSec_tens hr' (isRatSec_ratOfSec u hu)
  have K1 := swap_of_sec hI hR hq hd hT L M (N.tens A) s hs hr hp
  have K2 := swap_of_sec hI hR hq hd hT L M A u hu hr (isRatSec_ratOfSec u hu)
  have A3 := GlobalTheory.T.inductiveMixedHeight_tensor_additive hI k Y q hq e hd T hT M r hr N A L
  have A4 := add_first hI hR hq hd hT L M N A hr' (isRatSec_ratOfSec u hu) hp
  linarith

end GlobalTheory.MixHt.VSwap
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo : ArchInteg → ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (r' : N.B.ι → Y.functionFieldˣ) (hr' : IsRatSec N.B r'), recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N hr' := by
  atlas_forward_decl GlobalTheory.MixHt.VSwap.main
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.Step

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def extend (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) (V : (Fin (m + 1) → HermLB p) → X → ℝ) :
    ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ :=
  fun d L x => if h : d = m + 1 then V (fun a => L (Fin.cast h.symm a)) x else T d L x

theorem extend_of_ne {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    {d : ℕ} (h : d ≠ m + 1) (L : Fin d → HermLB p) (x : X) : extend m T V d L x = T d L x := dif_neg h

theorem extend_self {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    (L : Fin (m + 1) → HermLB p) (x : X) : extend m T V (m + 1) L x = V L x := by
  simp [extend]

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ} {h h' : Y → ℝ}
    (H : ∀ z, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem isRatSec_tens_mul {Z : Scheme.{0}} [IsIntegral Z] {A B : LB Z} {r : A.ι → Z.functionFieldˣ}
    {s : B.ι → Z.functionFieldˣ} (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem isMix_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  intro hI hR m hm k _ X p hp
  classical
  haveI : IsNoetherian X := hp.isNoetherian
  obtain ⟨T, hT⟩ := hm k X p hp
  choose v hv using GlobalTheory.T.mixedHeightRecursiveValue_well_defined hI hR m hm k X p hp T hT
  have hD := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  have hdimi : ∀ (Y : Scheme.{0}) [IsIntegral Y] (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ),
      topologicalKrullDim Y = (d : ℕ) → HasDim (i (genericPoint Y)) d := fun Y _ i _ d h =>
    (hD.2.2.2.2.1 Y i (genericPoint Y) d).2 ((hD.2.2.2.2.2 Y d).2 h)
  have hcd : ∀ x : X, HasDim x (m + 1) → topologicalKrullDim (clo x) = ((m + 1 : ℕ) : WithBot ℕ∞) := fun x hx =>
    (hD.2.2.2.2.2 (clo x) (m + 1)).1
      ((hD.2.2.2.2.1 (clo x) (cloι x) (genericPoint (clo x)) (m + 1)).1 (by rw [cloι_genericPoint]; exact hx))
  have E : ∀ (x : X) (hx : HasDim x (m + 1)) (M : HermLB p) (L : Fin m → HermLB p)
      (M' : HermLB (cloι x ≫ p)) (L' : Fin m → HermLB (cloι x ≫ p)),
      (M.pull (cloι x) rfl).Isometric M' → (∀ a, ((L a).pull (cloι x) rfl).Isometric (L' a)) →
      ∀ (r : M'.B.ι → (clo x).functionFieldˣ) (hr : IsRatSec M'.B r)
        (TY : ∀ d : ℕ, (Fin d → HermLB (cloι x ≫ p)) → clo x → ℝ), IsMix (cloι x ≫ p) m TY →
      v x hx M L = recVal (TY m L') L' M' hr := by
    intro x hx M L M' L' hM hL r hr TY hTY
    rw [hv x hx M L (clo x) (cloι x ≫ p) (cloι x) rfl (cloι_genericPoint x) M' L' hM hL r hr]
    refine recVal_congr (fun z hz => ?_) L' M' hr
    have hz' : HasDim z m := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo x) (cloι x ≫ p) (hp.sub _) m (hcd x hx)).1 z).1 hz
    exact GlobalTheory.T.mixedHeight_unique_restrict_closedSubscheme k X (clo x) p (cloι x ≫ p) hp (cloι x) rfl m m T TY hT hTY m le_rfl le_rfl L L' hL z hz'
  let V : (Fin (m + 1) → HermLB p) → X → ℝ := fun L x =>
    if hx : HasDim x (m + 1) then v x hx (L 0) (Fin.tail L) else 0
  have hV : ∀ (L : Fin (m + 1) → HermLB p) (x : X) (hx : HasDim x (m + 1)),
      extend m T V (m + 1) L x = v x hx (L 0) (Fin.tail L) := fun L x hx => by
    rw [extend_self]
    exact dif_pos hx
  have hsym : ∀ (x : X) (hx : HasDim x (m + 1)) (L : Fin (m + 1) → HermLB p) (e : Equiv.Perm (Fin (m + 1))),
      v x hx (L (e 0)) (Fin.tail fun a => L (e a)) = v x hx (L 0) (Fin.tail L) := by
    intro x hx L e
    obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
    have hq : IsAmb (cloι x ≫ p) := hp.sub (cloι x)
    have hdx := hcd x hx
    let F : (Fin (m + 1) → HermLB p) → ℝ := fun L => v x hx (L 0) (Fin.tail L)
    change F (fun a => L (e a)) = F L
    rcases m with _ | n
    · have : (fun a => L (e a)) = L := funext fun a => congrArg L (@Subsingleton.elim (Fin 1) _ _ _)
      rw [this]
    · refine GlobalTheory.T.perm_invariant_of_cons_swap_and_tail (HermLB p) n F (fun a L τ => ?_) (fun a b L => ?_) L e
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        rw [E x hx a (fun i => L (τ i)) (a.pull (cloι x) rfl) (fun i => (L (τ i)).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
          E x hx a L (a.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY]
        exact (GlobalTheory.T.mixedHeight_inductive_rhs_symm_isometry_invariant hI k (clo x) (cloι x ≫ p) hq (n + 1) hdx TY hTY _ ra hra).2.1
          (fun i => (L i).pull (cloι x) rfl) τ
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (b.pull (cloι x) rfl).isLB
        have iso : ∀ (c : HermLB p) (j : Fin (n + 1)), ((Fin.cons c L : Fin (n + 1) → HermLB p) j).pull (cloι x) rfl |>.Isometric
            ((Fin.cons (c.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl) : Fin (n + 1) → HermLB (cloι x ≫ p)) j) := by
          intro c j
          refine Fin.cases ?_ (fun i => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ] <;> exact HermLB.Isometric.refl _
        rw [E x hx a _ (a.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso b) ra hra TY hTY,
          E x hx b _ (b.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso a) rb hrb TY hTY]
        exact GlobalTheory.T.mixedHeightInduction_symmetric_firstTwo hI hR k (clo x) (cloι x ≫ p) hq n hdx TY hTY _ _ _ ra hra rb hrb
  refine ⟨extend m T V, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d L M x hd hx hLM
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨r, hr⟩ := Cartier.exists_isRatSec ((L 0).pull (cloι x) rfl).isLB
      rw [E x hx (L 0) (Fin.tail L) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr TY hTY,
        E x hx (M 0) (Fin.tail M) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          ((hLM 0).symm.pull _ _) (fun a => (hLM a.succ).symm.pull _ _) r hr TY hTY]
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.iso d L M x (by omega) hx hLM
  · intro d L e x hd hx
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      exact hsym x hx L e
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.symm d L e x (by omega) hx
  · intro d A B L x hd hx
    by_cases h : d + 1 = m + 1
    · obtain rfl : d = m := by omega
      rw [hV _ _ hx, hV _ _ hx, hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (A.pull (cloι x) rfl).isLB
      obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (B.pull (cloι x) rfl).isLB
      have ht := isRatSec_tens_mul hra hrb
      rw [E x hx (A.tens B) L ((A.pull (cloι x) rfl).tens (B.pull (cloι x) rfl)) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.isometric_pull_tens A B _ _) (fun _ => HermLB.Isometric.refl _) _ ht TY hTY,
        E x hx A L (A.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
        E x hx B L (B.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) rb hrb TY hTY]
      exact GlobalTheory.T.inductiveArakelovFormula_rhs_tensor_additive hI k (clo x) (cloι x ≫ p) (hp.sub _) d (hcd x hx) _ _ _ _ ra hra rb hrb _ ht
        fun _ _ _ _ => rfl
    · rw [extend_of_ne h, extend_of_ne h, extend_of_ne h]
      exact hT.add d A B L x (by omega) hx
  · intro L x hx
    rw [extend_of_ne (by omega)]
    exact hT.zero L x hx
  · intro Y _ _ q i _ hi e he hdim M L M' L' hM hL r hr
    have hfun : (fun z => extend m T V e L (i z)) = fun z => T e L (i z) :=
      funext fun z => extend_of_ne (by omega) L (i z)
    rw [hfun]
    by_cases h : e + 1 = m + 1
    · obtain rfl : e = m := by omega
      have hx := hdimi Y i (e + 1) hdim
      rw [hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      exact hv _ hx M L Y q i hi rfl M' L' hM hL r hr
    · rw [extend_of_ne h]
      exact hT.recur Y q i hi e (by omega) hdim M L M' L' hM hL r hr

end GlobalTheory.MixHt.Step
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMixedHeightByInduction_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  atlas_forward_decl GlobalTheory.MixHt.Step.isMix_succ
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem exists_isMix_of_arch : ArchInteg → ArchRecip →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  intro hI hR
  have key : ∀ m : ℕ, ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T := by
    intro m
    induction m with
    | zero => intro k _ Y q _; exact ⟨_, isMix_zero q⟩
    | succ m ih => exact GlobalTheory.T.isMixedHeightByInduction_succ hI hR m ih
  intro k _ Y q h m
  exact key m k Y q h

end GlobalTheory.MixHt

example : ArchInteg → ArchRecip → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) :=
  GlobalTheory.MixHt.exists_isMix_of_arch
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals : ArchInteg → ArchRecip → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  atlas_forward_decl GlobalTheory.MixHt.exists_isMix_of_arch
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arFormExists_of_isMix : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q →
    ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  intro hA hT k _ X _ p D hX ι _ L
  obtain ⟨T, hT⟩ := hT k X p (isAmb_of_isArithVar hX) (D + 1)
  have hg : HasDim (genericPoint X) (D + 1) :=
    ((GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p (isAmb_of_isArithVar hX)).2.2.2.2.2 X (D + 1)).2 hX.dim_eq
  obtain ⟨Φ, hΦ, hΦ0⟩ := GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive k X p D (fun M => T (D + 1) M (genericPoint X))
    (fun M N h => hT.iso (D + 1) M N _ le_rfl hg h)
    (fun M e => hT.symm (D + 1) M e _ le_rfl hg)
    (fun A B M => hT.add D A B M _ le_rfl hg) ι L
  refine ⟨Φ, fun n => ?_, hΦ0⟩
  obtain ⟨h, hh, hx⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hA k X p D hX T hT (comb L n)
  refine ⟨h, hh, ?_⟩
  rw [hx _ _ hg, ← Fin.prod_const (D + 1) (lin fun i => (n i : ℝ)), hΦ (fun _ => n)]

end GlobalTheory.MixHt
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  atlas_forward_decl GlobalTheory.MixHt.arFormExists_of_isMix
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory

theorem addMonoidHom_intCast_mul_real {A : Type} [CommRing A] (θ : A →+ ℝ) (k : ℤ) (z : A) :
    θ ((k : A) * z) = (k : ℝ) * θ z := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem polarisation_mixed_term_of_powers : ∀ (A : Type) [CommRing A] (θ : A →+ ℝ) (ι : Type) [Fintype ι] (x : Option ι → A) (D : ℕ) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), (∀ n : Option ι → ℤ, Φ (lin (fun o => (n o : ℝ)) ^ (D + 1)) = θ ((∑ o, n o • x o) ^ (D + 1))) → ∀ n : ι → ℤ, Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = θ ((∑ i, n i • x (some i)) ^ D * x none) := by
  intro A _ θ ι _ x D Φ h n
  set Y : MvPolynomial (Option ι) ℝ := MvPolynomial.X none with hY
  set L : MvPolynomial (Option ι) ℝ := rename some (lin fun i => (n i : ℝ)) with hL
  set y : A := ∑ i, n i • x (some i) with hy
  set P : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hP
  set Q : Polynomial ℝ := ∑ a ∈ Finset.range (D + 2),
    Polynomial.C (θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ)) * Polynomial.X ^ a with hQ
  have key : ∀ t : ℤ, P.eval (t : ℝ) = Q.eval (t : ℝ) := by
    intro t
    have ht := h (fun o => Option.elim o t n)
    have hlin : lin (fun o => ((Option.elim o t n : ℤ) : ℝ)) = MvPolynomial.C (t : ℝ) * Y + L := by
      simp only [lin, Fintype.sum_option, Option.elim, hY, hL, map_sum, map_mul, rename_C, rename_X]
    have hsum : (∑ o, (Option.elim o t n) • x o) = (t : A) * x none + y := by
      simp only [Fintype.sum_option, Option.elim, hy, zsmul_eq_mul]
    rw [hlin, hsum, add_pow, add_pow, map_sum, map_sum] at ht
    simp only [hP, hQ, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    have e1 : ∀ a : ℕ, Φ ((MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ))
        = Φ (Y ^ a * L ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : (MvPolynomial.C (t : ℝ) * Y) ^ a * L ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : MvPolynomial (Option ι) ℝ)
          = ((t : ℝ) ^ a * ((D + 1).choose a : ℝ)) • (Y ^ a * L ^ (D + 1 - a)) := by
        rw [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, mul_pow, map_natCast]
        ring
      rw [this, map_smul, smul_eq_mul]
      ring
    have e2 : ∀ a : ℕ, θ (((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A))
        = θ (x none ^ a * y ^ (D + 1 - a)) * ((D + 1).choose a : ℝ) * (t : ℝ) ^ a := by
      intro a
      have : ((t : A) * x none) ^ a * y ^ (D + 1 - a) * (((D + 1).choose a : ℕ) : A)
          = (((t ^ a * ((D + 1).choose a : ℤ)) : ℤ) : A) * (x none ^ a * y ^ (D + 1 - a)) := by
        push_cast
        ring
      rw [this, addMonoidHom_intCast_mul_real]
      push_cast
      ring
    simp only [e1, e2] at ht
    exact ht
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.Infinite.mono (s := Set.range (fun t : ℤ => (t : ℝ)))
    · rintro _ ⟨t, rfl⟩
      exact key t
    · exact Set.infinite_range_of_injective Int.cast_injective
  have hc := congrArg (fun p => Polynomial.coeff p 1) hPQ
  simp only [hP, hQ, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  simp only [Finset.sum_ite_eq, Finset.mem_range] at hc
  rw [if_pos (by omega), if_pos (by omega)] at hc
  · simp only [pow_one, Nat.choose_one_right, Nat.add_sub_cancel] at hc
    have hD : ((D + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    push_cast at hc hD
    have := mul_right_cancel₀ hD hc
    rw [mul_comm (y ^ D)]
    exact this

end GlobalTheory
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem isometric_pull_id {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) :
    (L.pull (𝟙 X) (Category.id_comp p)).Isometric L := by
  have hid {σ : k →+* ℂ} (y : CxPts p σ) : Points.PtsOver.map (𝟙 X) (Category.id_comp p) _ y = y :=
    Subtype.ext (Category.comp_id _)
  have hiso : L.Isometric (L.pull (𝟙 X) (Category.id_comp p)) := by
    refine HermLB.isometric_of_chart (fun c _ => c) (fun c y hy => Set.mem_iInter.2 fun _ => hy)
      (fun z c c' hc hc' => ?_) fun σ c y _ => ?_
    · refine Eq.trans ?_ (gm_pull_g L.B (𝟙 X) (𝟙 X) z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · exact ((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).trans (congrArg _ (hid y))
  exact hiso.symm

theorem hasDim_genericPoint {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) : HasDim (genericPoint X) (D + 1) :=
  (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id
    (Set.range_id.trans (genericPoint_spec X).def.symm)).trans hX.dim_eq

theorem hasDim_of_coheight_eq_one {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {z : X} (hz : Order.coheight z = 1) : HasDim z D := by
  obtain ⟨Z, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
  have hrange : Set.range i = closure {i (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  unfold HasDim
  rw [topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
  exact PrimeDivDim.dim_eq_of_coheight_eq_one k X p D hX Z i hz

theorem lin_intCast {ι : Type} [Fintype ι] (n : ι → ℤ) :
    lin (fun i => (n i : ℝ)) = ∑ i, n i • (MvPolynomial.X i : MvPolynomial ι ℝ) := by
  simp only [lin, zsmul_eq_mul, map_intCast]

theorem arMix_of_mixHt : ArchInteg →
    (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) →
    GlobalTheory.Published.ArMix := by
  intro hAI hEx k _ X _ _ p D hX ι _ M L Φ hΦ n h hh r hr
  refine ⟨hAI k X p D hX M (comb L n) r hr, ?_⟩
  obtain ⟨T, hT⟩ := hEx k X p (isAmb_of_isArithVar hX) (D + 1)
  have hgen := hasDim_genericPoint hX
  set F' : Option ι → HermLB p := fun o => o.elim M L with hF'
  let F : (Fin (D + 1) → HermLB p) → ℝ := fun K => T (D + 1) K (genericPoint X)
  obtain ⟨Φ₀, hΦ₀, -⟩ := GlobalTheory.T.exists_linear_functional_of_symmetric_multiadditive k X p D F (fun K K' hK => hT.iso _ K K' _ le_rfl hgen hK)
    (fun K e => hT.symm _ K e _ le_rfl hgen) (fun A B K => hT.add D A B K _ le_rfl hgen) (Option ι) F'

  have hpow : ∀ m : Option ι → ℤ, Φ (lin (fun o => (m o : ℝ)) ^ (D + 1)) =
      Φ₀.toAddMonoidHom ((∑ o, m o • (MvPolynomial.X o : MvPolynomial (Option ι) ℝ)) ^ (D + 1)) := by
    intro m
    obtain ⟨g, hg, hg'⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT (comb F' m)
    have h₁ : (comb F' m).IsSelfInter (T (D + 1) (fun _ => comb F' m) (genericPoint X)) :=
      ⟨g, hg, hg' _ _ hgen⟩
    have h₂ := hΦ₀ (fun _ => m)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h₂
    rw [HermLB.IsSelfInter.unique hX (hΦ.1 m) h₁, ← lin_intCast]
    exact h₂.symm
  have hpol := GlobalTheory.polarisation_mixed_term_of_powers (MvPolynomial (Option ι) ℝ) Φ₀.toAddMonoidHom ι MvPolynomial.X D Φ hpow n
  rw [hpol]

  let m₀ : Option ι → ℤ := fun o => o.elim 1 0
  let m₁ : Option ι → ℤ := fun o => o.elim 0 n
  have hprod : (∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D * MvPolynomial.X none =
      ∏ a : Fin (D + 1), lin (fun o => ((Fin.cons m₀ (fun _ => m₁) : Fin (D + 1) → Option ι → ℤ) a o : ℝ)) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, lin_intCast,
      Fintype.sum_option, m₀, m₁, Option.elim, zero_smul, zero_add, one_smul]
    simp only [Pi.zero_apply, Int.cast_zero, Int.cast_one, zsmul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one, one_mul]
    ring
  have hval : Φ₀.toAddMonoidHom ((∑ i, n i • (MvPolynomial.X (some i) : MvPolynomial (Option ι) ℝ)) ^ D *
      MvPolynomial.X none) = T (D + 1) (Fin.cons M (fun _ => comb L n)) (genericPoint X) := by
    rw [LinearMap.toAddMonoidHom_coe, hprod, hΦ₀]
    refine hT.iso _ _ _ _ le_rfl hgen fun a => ?_
    refine Fin.cases ?_ (fun a => ?_) a
    · simp only [Fin.cons_zero]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₀, F']
    · simp only [Fin.cons_succ]
      refine HermLB.icls_eq_iff.1 ?_
      simp [icls_comb, Fintype.sum_option, m₁, F']
  rw [hval]

  set N := comb L n
  have hrec := hT.recur X p (𝟙 X) (Category.id_comp p) D le_rfl hX.dim_eq M (fun _ => N) M (fun _ => N)
    (isometric_pull_id M) (fun _ => isometric_pull_id N) r hr
  have e₁ : (𝟙 X : X ⟶ X) (genericPoint X) = genericPoint X := by simp
  rw [e₁] at hrec
  rw [hrec, recVal, (GlobalTheory.T.mixedArchIntegral_additive_and_diagonal hAI k X p (isAmb_of_isArithVar hX) M r hr).2 D hX.dim_eq N]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  obtain ⟨g, hg, hg'⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hAI k X p D hX T hT N
  obtain rfl : h = g := hh.unique hX hg
  have e₂ : (𝟙 X : X ⟶ X) z = z := by simp
  rw [e₂, hg' z D (hasDim_of_coheight_eq_one hX (CartierDiv.coheight_eq_one_of_mult_ne_zero hz))]

end GlobalTheory.MixHt
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithMixedInterInductive_of_mixedHeights : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArMix := by
  atlas_forward_decl GlobalTheory.MixHt.arMix_of_mixHt
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHeight_projectionFormula_every_point : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ), IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ), L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  first | exact @GlobalTheory.MixHt.heightProj | exact GlobalTheory.MixHt.heightProj | (intros; apply GlobalTheory.MixHt.heightProj <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHtCalc

theorem arFormExists_arMix_heightProjection (hI : ArchInteg) (hR : ArchRecip) :
    GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  have hE := GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals hI hR
  refine ⟨GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights hI hE, GlobalTheory.T.arithMixedInterInductive_of_mixedHeights hI hE, ?_⟩
  intro k _ X Y _ p q D e hX hY π hπ _ _ L h hh
  obtain ⟨T, hT⟩ := hE k Y q (isAmb_of_isArithVar hY) (e + 1)
  obtain ⟨h', hh', -⟩ := GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal hI k Y q e hY T hT (L.pull π hπ)
  exact ⟨h', hh', GlobalTheory.T.arithHeight_projectionFormula_every_point k X Y p q D e hX hY π hπ L h h' hh hh' (genericPoint Y)⟩

end GlobalTheory.MixHtCalc
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersection_forms_of_archimedean_statements : ArchInteg → ArchRecip → GlobalTheory.Published.ArFormExists ∧ GlobalTheory.Published.ArMix ∧ GlobalTheory.Published.HeightProjection := by
  atlas_forward_decl GlobalTheory.MixHtCalc.arFormExists_arMix_heightProjection
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem arCalc_cycleHeights_of_analytic :
    ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := fun hI hR =>
  have h := GlobalTheory.T.arithIntersection_forms_of_archimedean_statements hI hR
  have hC : GlobalTheory.Published.ArCalc := GlobalTheory.Published.arCalc_of_form_mix_projection h.1 h.2.1 h.2.2
  ⟨hC, GlobalTheory.Published.cycleHeights_of_arCalc hC⟩

end GlobalTheory.MixHt
end

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithIntersectionCalculus_cycleHeights_of_analytic : ArchInteg → ArchRecip → GlobalTheory.Published.ArCalc ∧ GlobalTheory.Published.CycleHeights := by
  atlas_forward_decl GlobalTheory.MixHt.arCalc_cycleHeights_of_analytic
end
