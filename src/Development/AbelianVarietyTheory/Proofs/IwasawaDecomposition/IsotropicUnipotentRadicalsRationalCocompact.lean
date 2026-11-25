module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

namespace GlobalTheory.Mem.UnipCocompact

section Abstract

variable {S : Type} [Ring S] {st : S →+ S}

def cay (M : ℕ) (y : S) : S := (1 + y) * ∑ j ∈ Finset.range M, y ^ j

theorem cay_unitary (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) {M : ℕ} {y : S}
    (h0 : y ^ M = 0) (hy : st y = -y) : st (cay M y) * cay M y = 1 ∧ cay M y * st (cay M y) = 1 := by
  have h1 : st 1 = 1 := GlobalTheory.TwoStepUnipotent.st_one hm hi
  unfold cay
  generalize hG : ∑ j ∈ Finset.range M, y ^ j = G
  have a1 : (1 - y) * G = 1 := by rw [← hG, mul_neg_geom_sum, h0, sub_zero]
  have a2 : G * (1 - y) = 1 := by rw [← hG, geom_sum_mul_neg, h0, sub_zero]
  have b1 : st G * (1 + y) = 1 := by
    have := congrArg st a1
    rwa [hm, map_sub, h1, hy, sub_neg_eq_add] at this
  have b2 : (1 + y) * st G = 1 := by
    have := congrArg st a2
    rwa [hm, map_sub, h1, hy, sub_neg_eq_add] at this
  have c1 : st ((1 + y) * G) * ((1 + y) * G) = 1 := by
    rw [hm, map_add (f := _), h1, hy]
    calc st G * (1 + -y) * ((1 + y) * G) = (st G * (1 + y)) * ((1 - y) * G) := by noncomm_ring
      _ = 1 := by rw [a1, b1, one_mul]
  have c2 : ((1 + y) * G) * ((1 - y) * st G) = 1 := by
    rw [mul_assoc, ← mul_assoc G, a2, one_mul, b2]
  refine ⟨c1, ?_⟩
  rw [left_inv_eq_right_inv c1 c2, c2]

theorem cay_sub {M : ℕ} {y : S} (h0 : y ^ M = 0) :
    cay M y - 1 - (y + y) = (y + y) * ∑ j ∈ Finset.range M, y ^ (j + 1) := by
  unfold cay
  have e : ∑ j ∈ Finset.range M, y ^ (j + 1) = y * ∑ j ∈ Finset.range M, y ^ j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => pow_succ' y j
  rw [e]
  generalize hG : ∑ j ∈ Finset.range M, y ^ j = G
  have a1 : (1 - y) * G = 1 := by rw [← hG, mul_neg_geom_sum, h0, sub_zero]
  calc (1 + y) * G - 1 - (y + y) = (y + y) * (y * G) + ((1 - y) * G - 1) + (y + y) * ((1 - y) * G - 1) := by
        noncomm_ring
    _ = _ := by rw [a1]; simp

variable {ι : Type} [Fintype ι] (ε : ι → S) (w : ι → ℤ)

def raise (i : ℕ) : AddSubgroup S where
  carrier := {x | ∀ a b, w a ≤ w b + i → ε a * x * ε b = 0}
  zero_mem' := by simp
  add_mem' hx hy a b hab := by rw [mul_add, add_mul, hx a b hab, hy a b hab, add_zero]
  neg_mem' hx a b hab := by rw [mul_neg, neg_mul, hx a b hab, neg_zero]

variable {ε w}

theorem raise_mul (he : CompleteOrthogonalIdempotents ε) (i : ℕ) {x y : S} (hx : x ∈ raise ε w i) (hy : y ∈ raise ε w i) :
    x * y ∈ raise ε w (i + 1) := fun a b hab => by
  have : ε a * (x * y) * ε b = ∑ c, (ε a * x * ε c) * (ε c * y * ε b) := by
    calc ε a * (x * y) * ε b = ε a * x * (∑ c, ε c) * y * ε b := by rw [he.complete]; simp only [mul_one, mul_assoc]
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun c _ => ?_
        conv_lhs => rw [← (he.idem c).eq]
        simp only [mul_assoc]
  rw [this]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : w a ≤ w c + i
  · rw [hx a c h, zero_mul]
  · rw [hy c b (by push_cast at hab; omega), mul_zero]

omit [Fintype ι] in
theorem raise_le (i : ℕ) : raise ε w (i + 1) ≤ raise ε w i := fun _ hx a b hab => hx a b (by push_cast; omega)

omit [Fintype ι] in
theorem raise_st (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (hs : ∀ a, ∃ a', st (ε a) = ε a' ∧ w a' = - w a) (i : ℕ) {x : S} (hx : x ∈ raise ε w i) : st x ∈ raise ε w i :=
  fun a b hab => by
    obtain ⟨a', ha, wa⟩ := hs a
    obtain ⟨b', hb, wb⟩ := hs b
    have := congrArg st (hx b' a' (by omega))
    rwa [hm, hm, ← ha, ← hb, hi, hi, map_zero, ← mul_assoc] at this

theorem compact_mod_of_weights [TopologicalSpace S] [IsTopologicalRing S] (S₀ : Subring S) (h : S) (K : Set S)
    (hcont : Continuous st) (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x)
    (h0 : ∀ x ∈ S₀, st x ∈ S₀) (hh0 : h ∈ S₀) (hh : h + h = 1) (hc : ∀ x, h * x = x * h)
    (hK : IsCompact K) (hcov : ∀ x, ∃ y ∈ S₀, x - y ∈ K) (he : CompleteOrthogonalIdempotents ε)
    (he0 : ∀ a, ε a ∈ S₀) (hs : ∀ a, ∃ a', st (ε a) = ε a' ∧ w a' = - w a) :
    ∃ K' : Set S, IsCompact K' ∧ (∀ g ∈ K', (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0) ∧
      ∀ g, (st g * g = 1 ∧ g * st g = 1) ∧ g - 1 ∈ raise ε w 0 →
        ∃ γ ∈ S₀, ((st γ * γ = 1 ∧ γ * st γ = 1) ∧ γ - 1 ∈ raise ε w 0) ∧ ∃ k ∈ K', g = γ * k := by
  apply GlobalTheory.UnipFlagCore.compact_mod_of_weights <;> assumption

variable {κ : Type} [Fintype κ]

def fam (st : S →+ S) (u : κ → S) : Option (κ ⊕ κ) → S :=
  fun x => x.elim (1 - ∑ j, Sum.elim u (fun j => st (u j)) j) (Sum.elim u fun j => st (u j))

def wt (d : κ → ℕ) (M : ℕ) : Option (κ ⊕ κ) → ℤ :=
  fun x => x.elim 0 (Sum.elim (fun j => (M : ℤ) - d j) fun j => (d j : ℤ) - M)

theorem fam_complete (hm : ∀ x y, st (x * y) = st y * st x) {u : κ → S} (hu : OrthogonalIdempotents u)
    (h13 : ∀ i j, u i * st (u j) = 0) (h31 : ∀ i j, st (u i) * u j = 0) : CompleteOrthogonalIdempotents (fam st u) := by
  refine CompleteOrthogonalIdempotents.option ⟨?_, ?_⟩
  · rintro (j | j)
    · exact hu.idem j
    · exact (hm _ _).symm.trans (congrArg st (hu.idem j).eq)
  · rintro (i | i) (j | j) hij
    · exact hu.ortho fun e => hij (congrArg _ e)
    · exact h13 i j
    · exact h31 i j
    · refine (hm _ _).symm.trans ?_
      rw [hu.ortho (fun e => hij (congrArg _ e.symm)), map_zero]

theorem fam_st (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) (u : κ → S) (d : κ → ℕ) (M : ℕ) :
    ∀ a, ∃ a', st (fam st u a) = fam st u a' ∧ wt d M a' = - wt d M a := by
  rintro (_ | j | j)
  · refine ⟨none, ?_, by simp [wt]⟩
    simp [fam, GlobalTheory.TwoStepUnipotent.st_one hm hi, hi, add_comm]
  · exact ⟨some (.inr j), rfl, by simp [wt]⟩
  · exact ⟨some (.inl j), hi _, by simp [wt]⟩

theorem mem_raise_fam (hm : ∀ x y, st (x * y) = st y * st x) (hi : ∀ x, st (st x) = x) {u : κ → S}
    (he : CompleteOrthogonalIdempotents (fam st u)) {d : κ → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (x : S) :
    x ∈ raise (fam st u) (wt d M) 0 ↔ (1 - ∑ j, u j) * x * (1 - st (∑ j, u j)) = 0 ∧
      (∀ i j, d i ≤ d j → u j * x * u i = 0) ∧ ∀ i j, d i ≤ d j → u j * st x * u i = 0 := by
  apply GlobalTheory.UnipFlagCore.mem_raise_fam <;> assumption

end Abstract

section Concrete

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

theorem sandwich_eq_zero {A : Type} [CommRing A] {n r : ℕ} {C : Matrix (Fin n) (Fin r) A} {L : Matrix (Fin r) (Fin n) A}
    (hL : L * C = 1) (m : Matrix (Fin n) (Fin n) A) (i j : Fin r) :
    C * single j j (1 : A) * L * m * (C * single i i (1 : A) * L) = 0 ↔ (L * m * C) j i = 0 := by
  have e : C * single j j (1 : A) * L * m * (C * single i i (1 : A) * L) = C * single j i ((L * m * C) j i) * L := by
    have := Matrix.single_mul_mul_single j j i i (1 : A) (L * m * C) 1
    rw [one_mul, mul_one] at this
    rw [← this]; simp only [Matrix.mul_assoc]
  rw [e]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := congrArg (fun X => (L * X * C) j i) h
  simp only [← Matrix.mul_assoc, hL, Matrix.one_mul] at this
  rw [Matrix.mul_assoc _ L C, hL] at this
  simpa using this

theorem triangular_inv {A : Type} [CommRing A] {r : ℕ} (d : Fin r → ℕ) (X Y : Matrix (Fin r) (Fin r) A)
    (h : Y = -X - Y * X) (hX : ∀ i j, d i ≤ d j → X j i = 0) : ∀ i j, d i ≤ d j → Y j i = 0 := by
  intro i
  induction hi : d i using Nat.strong_induction_on generalizing i with
  | _ n ih =>
    intro j hij
    rw [h, Matrix.sub_apply, Matrix.neg_apply, hX i j (hi ▸ hij), Matrix.mul_apply, Finset.sum_eq_zero fun k _ => ?_]
    · simp
    · by_cases hk : d i ≤ d k
      · rw [hX i k hk, mul_zero]
      · rw [ih (d k) (by omega) k rfl j (by omega), zero_mul]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (V : HSpace E)

theorem perp_iff_idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E)
    (hL : L * C = 1) (m : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) :
    (∀ x : Fin V.rank → E, (cT (hc.sig : E →+* E) C * V.gram) *ᵥ x = 0 →
        ∃ a, m *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = C.map (inclR (F := F) (AF F)) *ᵥ a) ↔
      (1 - (C * L).map (inclR (F := F) (AF F))) * m * (1 - adj hc V ((C * L).map (inclR (F := F) (AF F)))) = 0 := by
  rw [adj_map]
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : V.gram⁻¹ * cT (hc.sig : E →+* E) (C * L) * V.gram =
      V.gram⁻¹ * cT (hc.sig : E →+* E) L * (cT (hc.sig : E →+* E) C * V.gram) := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  have hT : cT (hc.sig : E →+* E) C * V.gram * (V.gram⁻¹ * cT (hc.sig : E →+* E) L) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (gram_det_isUnit V), ← cT_mul, hL, cT_one]
  rw [e]
  generalize cT (hc.sig : E →+* E) C * V.gram = T at hT ⊢
  generalize V.gram⁻¹ * cT (hc.sig : E →+* E) L = P at hT ⊢
  have e1 : 1 - (P * T).map φ = (1 - P * T).map φ := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro h
    ext i k
    obtain ⟨a, ha⟩ := h (fun j => (1 - P * T : Matrix (Fin V.rank) (Fin V.rank) E) j k) (by
      have : T * (1 - P * T) = 0 := by
        rw [Matrix.mul_sub, ← Matrix.mul_assoc, hT, Matrix.mul_one, Matrix.one_mul, sub_self]
      funext j; exact congrFun (congrFun this j) k)
    have h2 : (1 - (C * L).map φ) * C.map φ = 0 := by
      rw [Matrix.sub_mul, Matrix.map_mul, Matrix.mul_assoc, hL', Matrix.mul_one, Matrix.one_mul, sub_self]
    have h3 := congrArg ((1 - (C * L).map φ) *ᵥ ·) ha
    simp only [Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec] at h3
    rw [e1]
    exact congrFun h3 i
  · intro h x hx
    refine ⟨(L.map φ * m) *ᵥ fun i => φ (x i), ?_⟩
    have h1 : (T.map φ) *ᵥ (fun i => φ (x i)) = 0 := by
      funext i
      have := RingHom.map_mulVec φ T x i
      rw [hx] at this
      simpa [Function.comp_def] using this.symm
    have h2 := congrArg (· *ᵥ fun i => φ (x i)) h
    simp only [Matrix.zero_mulVec] at h2
    rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.map_mul (L := P),
      ← Matrix.mulVec_mulVec _ (P.map φ), h1, Matrix.mulVec_zero, sub_zero, Matrix.sub_mul, Matrix.one_mul,
      Matrix.sub_mulVec, sub_eq_zero, Matrix.map_mul, Matrix.mul_assoc] at h2
    rw [h2, Matrix.mulVec_mulVec]

def radSet {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (d : Fin r → ℕ) : Set (GA hc V) :=
  {g | (∀ i, ∃ a : Fin r → AF F ⊗[F] E, (∀ j, d i ≤ d j → a j = 0) ∧
      ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun k => inclR (F := F) (AF F) (C k i)) = C.map (inclR (F := F) (AF F)) *ᵥ a) ∧
    ∀ x : Fin V.rank → E, (cT (hc.sig : E →+* E) C * V.gram) *ᵥ x = 0 →
      ∃ a, ((HA.mat _ hc.sig V.gram g).1 - 1) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) = C.map (inclR (F := F) (AF F)) *ᵥ a}

noncomputable def idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (j : Fin r) :
    Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E) := (C * single j j (1 : E) * L).map (inclR (F := F) (AF F))

theorem idem_eq {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (j : Fin r) :
    idem (F := F) V C L j = C.map (inclR (F := F) (AF F)) * single j j (1 : AF F ⊗[F] E) * L.map (inclR (F := F) (AF F)) := by
  rw [idem, Matrix.map_mul, Matrix.map_mul, Matrix.map_single, map_one]

theorem sum_idem {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) :
    ∑ j, idem (F := F) V C L j = (C * L).map (inclR (F := F) (AF F)) := by
  simp only [idem_eq]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one, Matrix.map_mul]

theorem idem_complete {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (hL : L * C = 1)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (hLL : L * V.gram⁻¹ * cT (hc.sig : E →+* E) L = 0) :
    CompleteOrthogonalIdempotents (fam (adj hc V) (idem V C L)) := by
  have e : ∀ j : Fin r, V.gram⁻¹ * cT (hc.sig : E →+* E) (C * single j j (1 : E) * L) * V.gram =
      V.gram⁻¹ * cT (hc.sig : E →+* E) L * cT (hc.sig : E →+* E) (single j j (1 : E)) *
        (cT (hc.sig : E →+* E) C * V.gram) := fun j => by
    rw [cT_mul, cT_mul]; simp only [Matrix.mul_assoc]
  have e2 : ∀ i j : Fin r, C * single i i (1 : E) * L * (C * single j j (1 : E) * L) = C * (single i i (1 : E) * single j j (1 : E)) * L :=
    fun i j => by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc L C, hL, Matrix.one_mul]
  refine fam_complete (adj_mul hc V) ⟨fun j => ?_, fun i j hij => ?_⟩ (fun i j => ?_) (fun i j => ?_)
  · show _ * _ = _
    rw [idem, ← Matrix.map_mul, e2, Matrix.single_mul_single_same, one_mul]
  · show _ * _ = _
    rw [idem, idem, ← Matrix.map_mul, e2, Matrix.single_mul_single_of_ne (h := hij)]
    simp
  · rw [idem, idem, adj_map, e, ← Matrix.map_mul]
    simp only [Matrix.mul_assoc] at hLL ⊢
    rw [← Matrix.mul_assoc V.gram⁻¹, ← Matrix.mul_assoc L, hLL]
    simp
  · rw [idem, idem, adj_map, e, ← Matrix.map_mul]
    simp only [Matrix.mul_assoc] at h0 ⊢
    rw [← Matrix.mul_assoc V.gram C, ← Matrix.mul_assoc (cT _ C), h0]
    simp

theorem adj_mat (g : GA hc V) : adj hc V (HA.mat _ hc.sig V.gram g).1 = (HA.mat _ hc.sig V.gram g⁻¹).1 := by
  have h := (adj_mul_self_iff hc V g.1).2 g.2
  exact (Units.inv_eq_of_mul_eq_one_left h).symm

theorem mem_radSet_iff {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (L : Matrix (Fin r) (Fin V.rank) E) (hL : L * C = 1)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (hLL : L * V.gram⁻¹ * cT (hc.sig : E →+* E) L = 0)
    {d : Fin r → ℕ} {M : ℕ} (hd : ∀ j, d j < M) (g : GA hc V) :
    g ∈ radSet hc V C d ↔ (HA.mat _ hc.sig V.gram g).1 - 1 ∈ raise (fam (adj hc V) (idem V C L)) (wt d M) 0 := by
  rw [mem_raise_fam (adj_mul hc V) (adj_adj hc V) (idem_complete hc V C L hL h0 hLL) hd, sum_idem,
    ← perp_iff_idem hc V C L hL, map_sub, adj_mat, GlobalTheory.TwoStepUnipotent.st_one (adj_mul hc V) (adj_adj hc V)]
  have hinv : (HA.mat _ hc.sig V.gram g⁻¹).1 * (HA.mat _ hc.sig V.gram g).1 = 1 := Units.inv_mul g.1
  unfold radSet
  rw [Set.mem_ofPred_eq]
  generalize (HA.mat _ hc.sig V.gram g⁻¹).1 = y at hinv ⊢
  generalize (HA.mat _ hc.sig V.gram g).1 = x at hinv ⊢
  set φ := inclR (F := F) (E := E) (AF F)
  have hL' : L.map φ * C.map φ = 1 := by rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  have sw : ∀ (m : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E)) (i j : Fin r),
      idem V C L j * m * idem V C L i = 0 ↔ (L.map φ * m * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = 0 :=
    fun m i j => by rw [idem_eq, idem_eq]; exact sandwich_eq_zero hL' m i j
  simp only [sw]
  have co : ∀ (i : Fin r) (a : Fin r → AF F ⊗[F] E), (x - 1) *ᵥ (fun k => φ (C k i)) = C.map φ *ᵥ a → ∀ j, (L.map φ * (x - 1) * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = a j :=
    fun i a ha j => by
      have := congrArg (L.map φ *ᵥ ·) ha
      simp only [Matrix.mulVec_mulVec, hL', Matrix.one_mulVec] at this
      exact congrFun this j
  constructor
  · rintro ⟨h1, h2⟩
    have k : ∀ i j : Fin r, d i ≤ d j → (L.map φ * (x - 1) * C.map φ : Matrix (Fin r) (Fin r) (AF F ⊗[F] E)) j i = 0 := fun i j hij => by
      obtain ⟨a, ha, ha'⟩ := h1 i
      rw [co i a ha', ha j hij]
    refine ⟨h2, k, triangular_inv d _ _ ?_ k⟩
    have e : (x - 1) * C.map φ = C.map φ * (L.map φ * (x - 1) * C.map φ) := by
      ext k i
      obtain ⟨a, -, ha'⟩ := h1 i
      rw [Matrix.mul_apply (M := C.map φ)]
      simp only [co i a ha']
      exact congrFun ha' k
    have e' : y - 1 = -(x - 1) - (y - 1) * (x - 1) := by
      rw [sub_mul, mul_sub, hinv]; noncomm_ring
    rw [Matrix.mul_assoc (L.map φ * (y - 1)), ← e]
    conv_lhs => rw [e']
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  · rintro ⟨h2, h1, -⟩
    refine ⟨fun i => ?_, h2⟩
    obtain ⟨a, ha⟩ := h2 (fun k => C k i) (funext fun j => congrFun (congrFun h0 j) i)
    exact ⟨a, fun j hij => by rw [← co i a ha, h1 i j hij], ha⟩

theorem closure_radSet_cocompact {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) E) (hC : LinearIndependent E Cᵀ)
    (h0 : cT (hc.sig : E →+* E) C * V.gram * C = 0) (d : Fin r → ℕ) :
    ∃ K : Set (Subgroup.closure (radSet hc V C d)), IsCompact K ∧
      ∀ n, ∃ γ ∈ (ratPts hc V).subgroupOf (Subgroup.closure (radSet hc V C d)), ∃ k ∈ K, n = γ * k := by
  obtain ⟨L, hL, hLL⟩ := exists_dual hc V C hC h0
  obtain ⟨M, hd⟩ : ∃ M, ∀ j, d j < M := by
    obtain ⟨M, hM⟩ := (Set.finite_range d).bddAbove
    exact ⟨M + 1, fun j => Nat.lt_succ_of_le (hM ⟨j, rfl⟩)⟩
  obtain ⟨K, hK, hKs⟩ := tens_cocompact (F := F) (E := E)
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  set φ := inclR (F := F) (E := E) (AF F) with hφ
  have he := idem_complete hc V C L hL h0 hLL
  have hs := fam_st (adj_mul hc V) (adj_adj hc V) (idem (F := F) V C L) d M
  have h1 := GlobalTheory.TwoStepUnipotent.st_one (adj_mul hc V) (adj_adj hc V)
  have hcont : Continuous (adj hc V) := (continuous_const.matrix_mul (continuous_id.matrix_map
      (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) hc.sig)).matrix_transpose).matrix_mul continuous_const
  have hst0 : ∀ x ∈ (φ.mapMatrix (m := Fin V.rank)).range, adj hc V x ∈ (φ.mapMatrix (m := Fin V.rank)).range := by
    rintro _ ⟨X, rfl⟩; exact ⟨_, (adj_map hc V X).symm⟩
  have hmem : ∀ g, g ∈ Subgroup.closure (radSet hc V C d) ↔
      (HA.mat _ hc.sig V.gram g).1 - 1 ∈ raise (fam (adj hc V) (idem V C L)) (wt d M) 0 := fun g => by
    refine ⟨fun hg => ?_, fun hg => Subgroup.subset_closure ((mem_radSet_iff hc V C L hL h0 hLL hd g).2 hg)⟩
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact (mem_radSet_iff hc V C L hL h0 hLL hd x).1 hx
    | one => exact (sub_self (1 : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E))).symm ▸ zero_mem _
    | mul x y _ _ hx hy =>
      have e : (HA.mat _ hc.sig V.gram (x * y)).1 = (HA.mat _ hc.sig V.gram x).1 * (HA.mat _ hc.sig V.gram y).1 := rfl
      rw [e]
      generalize (HA.mat _ hc.sig V.gram x).1 = a at hx ⊢
      generalize (HA.mat _ hc.sig V.gram y).1 = b at hy ⊢
      have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
      rw [this]
      exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
    | inv x _ hx =>
      have := raise_st (adj_mul hc V) (adj_adj hc V) hs 0 hx
      rwa [map_sub, adj_mat, h1] at this
  obtain ⟨K', hK', k1, k2⟩ := compact_mod_of_weights (st := adj hc V) (w := wt d M)
    (φ.mapMatrix (m := Fin V.rank)).range
    (Matrix.scalar _ (φ (1 / 2))) (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K) hcont
    (adj_mul hc V) (adj_adj hc V) hst0
    ⟨Matrix.scalar _ (1 / 2), by ext i j; by_cases h : i = j <;> simp [h]⟩
    (by rw [← map_add (f := _), ← map_add (f := _), add_halves, map_one, map_one])
    (fun x => (Matrix.scalar_commute _ (fun _ => Commute.all _ _) x).eq)
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK)
    (fun X => by
      choose y hy using fun i j => hKs (X i j)
      exact ⟨_, ⟨Matrix.of y, rfl⟩, fun i _ j _ => hy i j⟩) he
    (by
      have hu : ∀ j, idem (F := F) V C L j ∈ (φ.mapMatrix (m := Fin V.rank)).range := fun j => ⟨_, rfl⟩
      have hv : ∀ j : Fin r ⊕ Fin r, Sum.elim (idem (F := F) V C L) (fun j => adj hc V (idem V C L j)) j ∈
          (φ.mapMatrix (m := Fin V.rank)).range := by
        rintro (j | j)
        exacts [hu j, hst0 _ (hu j)]
      rintro (_ | j)
      exacts [sub_mem (one_mem _) (sum_mem fun j _ => hv j), hv j]) hs
  let lift : ∀ x : Matrix (Fin V.rank) (Fin V.rank) (AF F ⊗[F] E), (adj hc V x * x = 1 ∧ x * adj hc V x = 1) ∧
      x - 1 ∈ raise (fam (adj hc V) (idem V C L)) (wt d M) 0 → Subgroup.closure (radSet hc V C d) := fun x hx =>
    ⟨⟨⟨x, adj hc V x, hx.1.2, hx.1.1⟩, (adj_mul_self_iff hc V _).1 hx.1.1⟩, (hmem _).2 hx.2⟩
  let f : Subgroup.closure (radSet hc V C d) → _ := fun n => Units.embedProduct _ (HA.mat _ hc.sig V.gram n.1)
  have hf : Topology.IsInducing f :=
    Units.isInducing_embedProduct.comp (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal)
  refine ⟨f ⁻¹' ((fun x => (x, MulOpposite.op (adj hc V x))) '' K'),
    hf.isCompact_preimage' (hK'.image (continuous_id.prodMk (MulOpposite.continuous_op.comp hcont))) ?_, fun n => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨lift x (k1 x hx), rfl⟩
  · have u := (adj_mul_self_iff hc V _).2 n.1.2
    obtain ⟨γ, ⟨a, ha⟩, p1, k, hk, p2⟩ := k2 (HA.mat _ hc.sig V.gram n.1).1 ⟨⟨u, mul_eq_one_comm.1 u⟩, (hmem _).1 n.2⟩
    obtain ⟨b, hb⟩ := hst0 γ ⟨a, ha⟩
    refine ⟨lift γ p1, ?_, lift k (k1 k hk), ⟨k, hk, rfl⟩, Subtype.ext (Subtype.ext (Units.ext p2))⟩
    have inj : Function.Injective (φ.mapMatrix (m := Fin V.rank)) := Matrix.map_injective inclA_injective
    have hab : a * b = 1 := inj (by rw [map_mul, ha, hb, map_one, p1.1.2])
    refine ⟨⟨⟨a, b, hab, mul_eq_one_comm.1 hab⟩, inj ?_⟩, Subtype.ext (Units.ext ha)⟩
    have hγ' : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) hc.sig) γ * V.gram.map φ * γ = V.gram.map φ := (lift γ p1).1.2
    rw [← ha] at hγ'
    rw [map_mul, map_mul]
    exact (congrArg (· * V.gram.map φ * a.map φ) (GlobalTheory.AutFunCounterexample.cT_map_gen hc.sig a).symm).trans hγ'

end Concrete

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

theorem radicals_cocompact : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e → (∃ K : Set (NFlag B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NFlagQ B e, ∃ k ∈ K, n = γ * k) ∧ (∃ K : Set (NI B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NIQ B e, ∃ k ∈ K, n = γ * k) := by
  intro D B ρ e he
  have key : ∀ (d : Fin ρ → ℕ) (H : Subgroup (GA D B)), H = Subgroup.closure (radSet D.sp.cm B e d) →
      ∃ K : Set H, IsCompact K ∧ ∀ n, ∃ γ ∈ (GQ B).subgroupOf H, ∃ k ∈ K, n = γ * k := by
    rintro d _ rfl
    rw [GlobalTheory.AutFunCompare.GQ_eq]
    exact closure_radSet_cocompact D.sp.cm B e he.1 he.2 d
  refine ⟨key Fin.val _ rfl, key (fun _ => 0) _ ?_⟩
  have hs : (NI B e : Set (GA D B)) = radSet D.sp.cm B e fun _ => 0 := by
    ext g
    rw [GlobalTheory.AutFunCompare.NI_eq, SetLike.mem_coe, GlobalTheory.AutFunCompare.mem_unipRad_colSpan]
    refine and_congr ⟨fun h i => ⟨0, fun _ _ => rfl, ?_⟩, fun h => ?_⟩ Iff.rfl
    · rw [Matrix.mulVec_zero]
      exact funext fun k => congrFun (congrFun h k) i
    · ext k i
      obtain ⟨a, ha, h'⟩ := h i
      rw [show a = 0 from funext fun j => ha j le_rfl, Matrix.mulVec_zero] at h'
      exact congrFun h' k
  rw [← hs, Subgroup.closure_eq]

end GlobalTheory.Mem.UnipCocompact
