import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceTop
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.Rdata
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.RqLift
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IsClosedRank
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.PieceGood
import Mathlib
import GroundTheory.Brauer.DoubleCentralizer
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.Transfer
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.FrobeniusReciprocity.FrobProof

section
noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PAsm2

open Polynomial PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem conj_pow' {N : ℕ} (g : GL (Fin N) k) (y : Matrix (Fin N) (Fin N) k) (n : ℕ) :
    (g.val * y * g⁻¹.val) ^ n = g.val * y ^ n * g⁻¹.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

theorem roots_finite {N : ℕ} {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hZ : CR Z) {χ : k[X]} (hχ : χ ≠ 0) :
    {c : Matrix (Fin N) (Fin N) k | c ∈ Z ∧ aeval c χ = 0}.Finite := by
  letI : CommRing Z := { (inferInstance : Ring ↥Z) with mul_comm := fun a b => Subtype.ext (hZ.1 a a.2 b b.2) }
  haveI : IsReduced Z := hZ.2
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  have hT : {c : Z | aeval c χ = 0}.Finite := by
    refine Set.Finite.of_finite_image ?_ (IsArtinianRing.equivPi Z).injective.injOn
    refine (Set.Finite.pi (t := fun I : MaximalSpectrum Z => χ.rootSet (Z ⧸ I.asIdeal))
      fun I => χ.rootSet_finite _).subset ?_
    rintro _ ⟨c, hc, rfl⟩
    refine Set.mem_univ_pi.2 fun I => ?_
    rw [mem_rootSet_of_ne hχ, IsArtinianRing.equivPi_apply]
    have h := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ k I.asIdeal) c χ
    rw [show aeval c χ = 0 from hc, map_zero] at h
    exact h
  refine (hT.image Subtype.val).subset ?_
  rintro c ⟨hc, h0⟩
  refine ⟨⟨c, hc⟩, ?_, rfl⟩
  show aeval (⟨c, hc⟩ : Z) χ = 0
  exact Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact h0)

theorem root_of_nil {N : ℕ} {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hZ : CR Z) {χ : k[X]}
    {x c : Matrix (Fin N) (Fin N) k} (hx : x ∈ Bz Z) (hc : c ∈ Z) (hχx : aeval x χ = 0)
    (hn : IsNilpotent (x - c)) : aeval c χ = 0 := by
  have hxc : x * c = c * x := (hx c hc).symm
  have hcomm : ∀ a ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ ({x, c} : Set (Matrix (Fin N) (Fin N) k)),
      a * b = b * a := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxc
    · exact hxc.symm
    · rfl
  letI : CommRing (Algebra.adjoin k ({x, c} : Set (Matrix (Fin N) (Fin N) k))) :=
    Algebra.adjoinCommRingOfComm k hcomm
  let A := Algebra.adjoin k ({x, c} : Set (Matrix (Fin N) (Fin N) k))
  let xa : A := ⟨x, Algebra.subset_adjoin (by simp)⟩
  let ca : A := ⟨c, Algebra.subset_adjoin (by simp)⟩
  have hna : IsNilpotent (xa - ca) := (IsNilpotent.map_iff (f := A.val) Subtype.val_injective).1 hn
  have h1 := isNilpotent_aeval_sub_of_isNilpotent_sub χ hna
  have h2 : aeval xa χ = 0 := Subtype.ext (by rw [Polynomial.aeval_subalgebra_coe]; exact hχx)
  have h3 : IsNilpotent (aeval ca χ) := by simpa [h2] using h1.neg
  have h4 : IsNilpotent (aeval c χ) := by
    have := h3.map A.val
    rwa [← Polynomial.aeval_algHom_apply] at this
  let c' : Z := ⟨c, hc⟩
  have h5 : IsNilpotent (aeval c' χ) := by
    refine (IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 ?_
    rw [← Polynomial.aeval_algHom_apply]
    exact h4
  have h6 : aeval c' χ = 0 := by
    haveI : IsReduced Z := hZ.2
    exact h5.eq_zero
  have h7 := congrArg Subtype.val h6
  rwa [Polynomial.aeval_subalgebra_coe] at h7

variable (k) in

theorem pieceGood_of (hF : PositivityTheory.PfBern.Frob.FrobeniusReciprocity) (hS : Sect k) (hP : PieceTop k) (hD : Dich k)
    (hT : Transfer k) : PieceGood k := by
  classical
  intro p _ _ hU N q Z hZ hq hR hB χ
  by_cases hχ : χ.Monic ∧ χ.natDegree = N
  swap
  · refine ⟨0, Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0, fun x _ hc => ?_⟩, fun i => i.elim0⟩
    exact (hχ ⟨hc ▸ x.charpoly_monic, by rw [← hc, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]⟩).elim
  obtain ⟨D⟩ := hS p N q Z hZ hq hR hB χ hχ.1 hχ.2
  have hfin := roots_finite hZ hχ.1.ne_zero
  have hrt : ∀ j : Fin hfin.toFinset.card, (hfin.toFinset.equivFin.symm j).1 ∈ Z ∧
      aeval (hfin.toFinset.equivFin.symm j).1 χ = 0 := fun j => hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm j).2
  let rt : Fin hfin.toFinset.card → Matrix (Fin N) (Fin N) k := fun j => (hfin.toFinset.equivFin.symm j).1
  have rt_inj : Function.Injective rt := fun j j' h => hfin.toFinset.equivFin.symm.injective (Subtype.ext h)
  have hred : ∀ c ∈ Z, IsNilpotent c → c = 0 := fun c hc hn => by
    have h : IsNilpotent (⟨c, hc⟩ : Z) := (IsNilpotent.map_iff (f := Z.val) Subtype.val_injective).1 hn
    haveI : IsReduced Z := hZ.2
    exact congrArg Subtype.val h.eq_zero
  have hcz : ∀ c ∈ Z, ∀ x ∈ Bz Z, x - c ∈ Bz Z := fun c hc x hx a ha => by
    rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]
  let e := (finFunctionFinEquiv (m := N + 1) (n := D.m)).symm
  let τ : Fin ((N + 1) ^ D.m) → Fin D.m → ℕ := fun i t => (e i t : ℕ)
  have τ_inj : Function.Injective τ := fun i j h => e.injective (funext fun t => Fin.ext (congrFun h t))
  let bad : Fin ((N + 1) ^ D.m) → Prop := fun i => ∃ x₀ ∈ piece D (τ i), mu (Sx D x₀) < mu Z
  let G : Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card) → Set (Matrix (Fin N) (Fin N) k) := fun is =>
    if bad is.1 then (if is.2 = none then piece D (τ is.1) else ∅)
    else is.2.elim ∅ (fun j => {x | x ∈ piece D (τ is.1) ∧ (x - rt j) ^ q = 0})
  have hsub : ∀ is x, x ∈ G is → x ∈ piece D (τ is.1) := by
    rintro ⟨i, s⟩ x hx
    simp only [G] at hx
    split_ifs at hx
    · exact hx
    · simp at hx
    · cases s with
      | none => simp at hx
      | some j => exact hx.1
  have huniq : ∀ is js x, x ∈ G is → x ∈ G js → is = js := by
    rintro ⟨i, s⟩ ⟨j, t⟩ x hx hy
    have hij : i = j := τ_inj ((hsub _ x hx).2.2.symm.trans (hsub _ x hy).2.2)
    subst hij
    have hxB : x ∈ Bz Z := (hsub _ x hx).1
    simp only [G] at hx hy
    by_cases hb : bad i
    · rw [if_pos hb] at hx hy
      split_ifs at hx hy with h1 h2
      · rw [h1, h2]
      · simp at hy
      · simp at hx
      · simp at hx
    · rw [if_neg hb] at hx hy
      cases s with
      | none => simp at hx
      | some a =>
        cases t with
        | none => simp at hy
        | some b =>
          have ha : IsNilpotent (x - rt a) := ⟨q, hx.2⟩
          have hb' : IsNilpotent (x - rt b) := ⟨q, hy.2⟩
          have hca : Commute (rt a) x := hxB _ (hrt a).1
          have hcb : Commute (rt b) x := hxB _ (hrt b).1
          have hab : Commute (rt b) (rt a) := hZ.1 _ (hrt b).1 _ (hrt a).1
          have hcomm : Commute (x - rt b) (x - rt a) :=
            ((Commute.refl x).sub_right hca.symm).sub_left (hcb.sub_right hab)
          have hn : IsNilpotent (rt a - rt b) := by
            have := hcomm.isNilpotent_sub hb' ha
            rwa [sub_sub_sub_cancel_left] at this
          have h0 := hred _ (Z.sub_mem (hrt a).1 (hrt b).1) hn
          rw [rt_inj (sub_eq_zero.1 h0)]
  have hclosed : ∀ is, IsClosed (G is) := by
    rintro ⟨i, s⟩
    simp only [G]
    split_ifs
    · exact (hP N q Z hZ χ D (τ i)).1
    · exact isClosed_empty
    · cases s with
      | none => exact isClosed_empty
      | some j =>
        exact (hP N q Z hZ χ D (τ i)).1.inter
          (isClosed_eq ((continuous_id.sub continuous_const).pow q) continuous_const)
  have hinvar : ∀ is, ∀ g ∈ Gz Z, ∀ x ∈ G is, g.val * x * g⁻¹.val ∈ G is := by
    rintro ⟨i, s⟩ g hg x hx
    have hP2 := (hP N q Z hZ χ D (τ i)).2.1 g hg
    simp only [G] at hx ⊢
    split_ifs at hx ⊢
    · exact hP2 x hx
    · simp at hx
    · cases s with
      | none => simp at hx
      | some j =>
        refine ⟨hP2 x hx.1, ?_⟩
        have e1 : g.val * x * g⁻¹.val - rt j = g.val * (x - rt j) * g⁻¹.val := by
          rw [mul_sub, sub_mul, ← hg (rt j) (hrt j).1, mul_assoc (rt j), Units.mul_inv, mul_one]
        rw [e1, conj_pow', hx.2, mul_zero, zero_mul]
  have hcover : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ is, x ∈ G is := by
    intro x hx hc
    have hle : ∀ t, typ D x t < N + 1 := fun t =>
      Nat.lt_succ_of_le ((Matrix.rank_le_width _).trans (by simp))
    let i := e.symm fun t => ⟨typ D x t, hle t⟩
    have hxp : x ∈ piece D (τ i) :=
      ⟨hx, by rw [← hc]; exact Matrix.aeval_self_charpoly x, by funext t; simp [τ, i]⟩
    by_cases hb : bad i
    · refine ⟨(i, none), ?_⟩
      simp only [G, if_pos hb, if_true]
      exact hxp
    · rcases hD N q Z hZ χ D (τ i) x hxp with h | ⟨c, hc, hn⟩
      · exact (hb ⟨x, hxp, h⟩).elim
      · have hroot : aeval c χ = 0 := root_of_nil hZ hx hc hxp.2.1 hn
        have hmem : c ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨hc, hroot⟩
        refine ⟨(i, some (hfin.toFinset.equivFin ⟨c, hmem⟩)), ?_⟩
        have hrtc : rt (hfin.toFinset.equivFin ⟨c, hmem⟩) = c := by simp [rt]
        simp only [G, if_neg hb, Option.elim_some]
        refine ⟨hxp, ?_⟩
        rw [hrtc]
        exact hB _ (hcz c hc x hx) hn
  have hgood : ∀ is, Good Z (G is) := by
    rintro ⟨i, s⟩
    simp only [G]
    split_ifs with h1
    · obtain ⟨x₀, hx₀, hlt⟩ := h1
      exact Or.inr ⟨N, Sx D x₀, (hP N q Z hZ χ D (τ i)).2.2 x₀ hx₀, hlt, hT hF p hU N q Z hZ χ D (τ i) x₀ hx₀⟩
    · exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩
    · cases s with
      | none => exact Or.inl ⟨0, Z.zero_mem, fun x hx => by simp at hx⟩
      | some j => exact Or.inl ⟨rt j, (hrt j).1, fun x hx => ⟨q, hx.2⟩⟩
  let eqv := Fintype.equivFin (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card))
  refine ⟨Fintype.card (Fin ((N + 1) ^ D.m) × Option (Fin hfin.toFinset.card)), fun i => G (eqv.symm i),
    ⟨fun i => ⟨hclosed _, fun x hx => (hsub _ x hx).1, hinvar _⟩,
      fun i j hij => Set.disjoint_left.2 fun x h1 h2 => hij (eqv.symm.injective (huniq _ _ x h1 h2)),
      fun x hx hc => ?_⟩, fun i => hgood _⟩
  obtain ⟨is, his⟩ := hcover x hx hc
  exact ⟨eqv is, by simpa using his⟩

end PositivityTheory.RgUd.TP.Desc.Piece.PAsm2

end
end

section
noncomputable section

open Matrix Polynomial Module

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece

open ValuativeRel in

theorem twFin (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p c : ℕ) [Fact p.Prime] [CharP k p] : FiniteDimensional k (Tw k p c) := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  have hc : CompleteSpace k := inferInstance
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  have : CompleteSpace k := hc
  letI : TopologicalSpace (Tw k p c) := inferInstanceAs (TopologicalSpace k)
  have : IsTopologicalAddGroup (Tw k p c) := inferInstanceAs (IsTopologicalAddGroup k)
  have : T2Space (Tw k p c) := inferInstanceAs (T2Space k)
  have : LocallyCompactSpace (Tw k p c) := inferInstanceAs (LocallyCompactSpace k)
  have : ContinuousSMul k (Tw k p c) := ⟨by
    show Continuous fun q : k × k => (iterateFrobenius k p c q.1) * q.2
    simp only [iterateFrobenius_def]
    exact (continuous_fst.pow _).mul continuous_snd⟩
  exact FiniteDimensional.of_locallyCompactSpace k

theorem pad {M : Type*} [AddCommMonoid M] {q d : ℕ} (hqd : q ≤ d) (f : Fin q → M) :
    ∑ l : Fin q, f l = ∑ l : Fin d, if h : (l : ℕ) < q then f ⟨l, h⟩ else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if h : n < q then f ⟨n, h⟩ else 0) d]
  rw [← Finset.sum_subset (Finset.range_subset_range.2 hqd) (fun n _ hn => by
    rw [Finset.mem_range] at hn; rw [dif_neg hn])]
  rw [← Fin.sum_univ_eq_sum_range (fun n => if h : n < q then f ⟨n, h⟩ else 0) q]
  exact Finset.sum_congr rfl fun l _ => by rw [dif_pos l.2]

theorem sect (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Sect k := by
  intro p _ _ N q Z hZ hqc hroots hnilb χ hχm hχd
  obtain ⟨c, rfl⟩ := hqc
  haveI := twFin k p c
  letI : CommRing Z := { (inferInstance : Ring Z) with
    mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }
  haveI : IsReduced Z := hZ.2
  haveI : FiniteDimensional k Z := inferInstance
  haveI := rq_fin (A := Z) χ hχm (p ^ c)
  haveI := rq_pir (A := Z) χ (p ^ c)
  have hnilR : ∀ r : Rq Z χ (p ^ c), IsNilpotent r → r ^ (p ^ c) = 0 := rq_nil χ (p ^ c)
  have hrootR : ∀ a : k, ∃ w : Rq Z χ (p ^ c), w ^ (p ^ c) = algebraMap k _ a := by
    intro a
    obtain ⟨w, hw, hwa⟩ := hroots a
    refine ⟨Ideal.Quotient.mk _ (C ⟨w, hw⟩), ?_⟩
    have h1 : (⟨w, hw⟩ : Z) ^ (p ^ c) = algebraMap k Z a := Subtype.ext (by simpa using hwa)
    rw [← map_pow, ← map_pow, h1]
    rfl
  obtain ⟨r, s, c', u, ε, m, κ, h1, hu, hε, hrep, hid, hsum, horth, hcorner⟩ :=
    rdata (R := Rq Z χ (p ^ c)) p c hnilR hrootR
  have hdN : χ.natDegree ≤ max N (p ^ c) := hχd ▸ le_max_left _ _
  have hdq : p ^ c ≤ max N (p ^ c) := le_max_right _ _
  choose ar har using fun j => rq_rep (A := Z) χ hχm (p ^ c) (max N (p ^ c)) hdN (s j)
  obtain ⟨br, hbr⟩ := rq_rep (A := Z) χ hχm (p ^ c) (max N (p ^ c)) hdN ε
  choose γ0 hγ0 using fun i => hrep (Ideal.Quotient.mk _ (C (Module.finBasis k Z i)))
  obtain ⟨β0, hβ0⟩ := hrep (Ideal.Quotient.mk _ X)
  let ext : (Fin (p ^ c) → Fin r → k) → Fin (max N (p ^ c)) → Fin r → k :=
    fun g l j => if h : (l : ℕ) < p ^ c then g ⟨l, h⟩ j else 0
  let E : Fin m → Rq Z χ (p ^ c) := fun t => ∑ j, κ t j • s j
  refine ⟨{
    r := r
    d := max N (p ^ c)
    a := fun j l => (ar j l : Matrix (Fin N) (Fin N) k)
    ha := fun j l => (ar j l).2
    b := fun l => (br l : Matrix (Fin N) (Fin N) k)
    hb := fun l => (br l).2
    c := c'
    u := u
    a0 := finrank k Z
    z := fun i => (Module.finBasis k Z i : Matrix (Fin N) (Fin N) k)
    hz := ?_
    γ := fun i => ext (γ0 i)
    β := ext β0
    m := m
    κ := κ
    dd := fun t => finrank k (Submodule.span k (Set.range fun j => E t * s j))
    K := fun t => LinearMap.ker ((LinearMap.mulLeft k (E t)).comp (Fintype.linearCombination k s))
    spec := ?_ }⟩
  · apply le_antisymm
    · intro y hy
      have h := congrArg Subtype.val ((Module.finBasis k Z).sum_repr ⟨y, hy⟩)
      simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h
      rw [← h]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · exact Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (Module.finBasis k Z i).2)
  · intro x hx hχx
    have hB : ∀ P : Z[X], P.eval₂ Z.val.toRingHom x ∈ Bz Z := by
      intro P a ha
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ => rw [eval₂_add, mul_add, add_mul, hP, hQ]
      | monomial n b =>
        rw [eval₂_monomial]
        have e1 : a * (b : Matrix (Fin N) (Fin N) k) = b * a := hZ.1 a ha b b.2
        have e2 : Commute a (x ^ n) := Commute.pow_right (hx a ha) n
        show a * ((b : Matrix (Fin N) (Fin N) k) * x ^ n) = (b : Matrix (Fin N) (Fin N) k) * x ^ n * a
        rw [← mul_assoc, e1, mul_assoc, e2.eq, mul_assoc]
    obtain ⟨ρ, hρ⟩ := rq_lift (A := Z) Z.val x (fun a => hx a a.2) χ hχx (p ^ c)
      (fun P hP => hnilb _ (hB P) hP)
    have hpe : ∀ g : Fin (max N (p ^ c)) → Z, pe (fun l => (g l : Matrix (Fin N) (Fin N) k)) x =
        ρ (Ideal.Quotient.mk _ (∑ l : Fin (max N (p ^ c)), C (g l) * X ^ (l : ℕ))) := by
      intro g
      rw [hρ, eval₂_finset_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [C_mul_X_pow_eq_monomial, eval₂_monomial]
      rfl
    have hs : ∀ j, pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x = ρ (s j) := fun j => by
      rw [hpe, ← har j]
    have hε' : pe (fun l => (br l : Matrix (Fin N) (Fin N) k)) x = ρ ε := by rw [hpe, ← hbr]
    have hlin : ∀ v : Fin r → k, ∑ j, v j • ρ (s j) = ρ (∑ j, v j • s j) := fun v => by
      rw [map_sum]; simp only [map_smul]
    have hspan : ∀ y, y ∈ Submodule.span k (Set.range fun j => ρ (s j)) →
        ∃ v : Fin r → k, y = ρ (∑ j, v j • s j) := by
      intro y hy
      obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hy
      exact ⟨v, by rw [← hv, hlin]⟩
    have hE : ∀ t, ∑ j, κ t j • ρ (s j) = ρ (E t) := fun t => hlin (κ t)
    have hsum' : ∑ t, E t = 1 := hsum
    have hid' : ∀ t, IsIdempotentElem (E t) := hid
    have hcor : ∀ t (v : Fin r → k), (∑ j, v j • s j) * E t = 0 ∨
        ∃ w : Rq Z χ (p ^ c), (∑ j, v j • s j) * E t * w = E t := hcorner
    have hre : ∀ g : Fin (p ^ c) → Fin r → k, re (ext g) (fun j => ρ (s j)) (ρ ε) =
        ρ (∑ l, ∑ j, g l j • (s j * ε ^ (l : ℕ))) := by
      intro g
      rw [map_sum, pad hdq]
      unfold re
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases h : (l : ℕ) < p ^ c
      · rw [dif_pos h, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [ext, dif_pos h, map_smul, map_mul, map_pow]
      · rw [dif_neg h]
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [ext, dif_neg h, zero_smul]
    have nilmul : ∀ a b : Matrix (Fin N) (Fin N) k, Commute a b → IsNilpotent a → IsNilpotent (a * b) :=
      fun a b h ⟨n, hn⟩ => ⟨n, by rw [h.mul_pow, hn, zero_mul]⟩
    have hcomm : ∀ a b : Rq Z χ (p ^ c), Commute (ρ a) (ρ b) := fun a b => (Commute.all a b).map ρ
    dsimp only
    simp only [hs, hε']
    refine ⟨fun j j' => ?_, ?_, fun j j' => ?_, fun j => ?_, ?_, ?_, fun i => ?_, ?_, fun t => ?_, ?_,
      fun t t' htt => ?_, fun t y hy hyi hye => ?_, fun t => ?_, fun v => ?_⟩
    · rw [← map_mul, h1 j j', map_sum]; simp only [map_smul]
    · rw [hlin, hu, map_one]
    · rw [← map_mul, mul_comm, map_mul]
    · rw [← map_mul, mul_comm, map_mul]
    · rw [← map_pow, hε, map_zero]
    · intro y hy hnil
      obtain ⟨v, rfl⟩ := hspan y hy
      have hz0 : ∀ t, ρ ((∑ j, v j • s j) * E t) = 0 := by
        intro t
        rcases hcor t v with h | ⟨w', hw'⟩
        · rw [h, map_zero]
        · have hEn : IsNilpotent (ρ (E t)) := by
            rw [← hw', mul_assoc, map_mul]
            exact nilmul _ _ (hcomm _ _) hnil
          have hE0 : ρ (E t) = 0 := by
            obtain ⟨n, hn⟩ := hEn
            have := ((hid' t).map ρ).pow_succ_eq n
            rw [pow_succ, hn, zero_mul] at this
            exact this.symm
          rw [← (hid' t).eq, ← mul_assoc, map_mul, hE0, mul_zero]
      rw [← mul_one (∑ j, v j • s j), ← hsum', Finset.mul_sum, map_sum]
      exact Finset.sum_eq_zero fun t _ => hz0 t
    · rw [hre, ← hγ0 i, hρ, eval₂_C]
      rfl
    · rw [hre, ← hβ0, hρ, eval₂_X]
    · rw [hE]; exact (hid' t).map ρ
    · simp only [hE]; rw [← map_sum, hsum', map_one]
    · rw [hE, hE, ← map_mul, horth t t' htt, map_zero]
    · rw [hE] at hye ⊢
      obtain ⟨v, rfl⟩ := hspan y hy
      rcases hcor t v with h | ⟨w', hw'⟩
      · left; rw [← hye, ← map_mul, h, map_zero]
      · right
        have e1 : ρ (E t) = ρ (∑ j, v j • s j) * ρ (E t) * ρ w' := by rw [← map_mul, ← map_mul, hw']
        rw [hye] at e1
        calc ρ (∑ j, v j • s j) = ρ (∑ j, v j • s j) * ρ (E t) := hye.symm
          _ = ρ (∑ j, v j • s j) * (ρ (∑ j, v j • s j) * ρ w') := by rw [← e1]
          _ = ρ (∑ j, v j • s j) * ρ w' := by rw [← mul_assoc, hyi.eq]
          _ = ρ (E t) := e1.symm
    · have hfun : (fun j => (∑ j', κ t j' • pe (fun l => (ar j' l : Matrix (Fin N) (Fin N) k)) x) *
          pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x) = fun j => ρ (E t) * ρ (s j) := by
        funext j; simp only [hs, hE]
      have hE2 : ∑ j, κ t j • pe (fun l => (ar j l : Matrix (Fin N) (Fin N) k)) x = ρ (E t) := by
        simp only [hs, hE]
      rw [hfun, hE2]
      have hmap : Submodule.span k (Set.range fun j => ρ (E t) * ρ (s j)) =
          (Submodule.span k (Set.range fun j => E t * s j)).map ρ.toLinearMap := by
        rw [Submodule.map_span, ← Set.range_comp]
        congr 1
        ext j
        simp [map_mul]
      split_ifs with h0
      · have : (fun j => ρ (E t) * ρ (s j)) = fun _ => 0 := by funext j; rw [h0, zero_mul]
        rw [this, Submodule.span_eq_bot.2 (by rintro _ ⟨j, rfl⟩; rfl), finrank_bot]
      · rw [hmap]
        set V := Submodule.span k (Set.range fun j => E t * s j)
        have hinj : Function.Injective (ρ.toLinearMap.comp V.subtype) := by
          rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
          rintro ⟨y, hyV⟩ hy0
          obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hyV
          have hy2 : y = (∑ j, v j • s j) * E t := by
            rw [← hv, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_mul_assoc, mul_comm]
          have hy0' : ρ y = 0 := hy0
          rcases hcor t v with h | ⟨w', hw'⟩
          · exact Subtype.ext (show y = 0 by rw [hy2, h])
          · exact absurd (by rw [← hw', map_mul, ← hy2, hy0', zero_mul]) h0
        rw [← LinearMap.finrank_range_of_inj hinj, LinearMap.range_comp, Submodule.range_subtype]
    · simp only [hE, hlin, LinearMap.mem_ker, LinearMap.comp_apply, Fintype.linearCombination_apply,
        LinearMap.mulLeft_apply]
      constructor
      · intro h0 t hEt
        rcases hcor t v with h | ⟨w', hw'⟩
        · rw [mul_comm]; exact h
        · exact absurd (by rw [← hw', map_mul, map_mul, h0, zero_mul, zero_mul]) hEt
      · intro h
        rw [← mul_one (∑ j, v j • s j), ← hsum', Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero fun t _ => ?_
        by_cases hEt : ρ (E t) = 0
        · rw [map_mul, hEt, mul_zero]
        · rw [mul_comm, h t hEt, map_zero]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect
end
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

def Cx (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)) (x : Matrix (Fin N) (Fin N) k) : Subalgebra k (Matrix (Fin N) (Fin N) k) :=
  Algebra.adjoin k (insert x (Z : Set (Matrix (Fin N) (Fin N) k)))

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {x : Matrix (Fin N) (Fin N) k}

theorem cx_gens (hZ : CR Z) (hx : x ∈ Bz Z) :
    ∀ a ∈ insert x (Z : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ insert x (Z : Set (Matrix (Fin N) (Fin N) k)),
      a * b = b * a := by
  intro a ha b hb
  rcases Set.mem_insert_iff.1 ha with h1 | h1
  · rcases Set.mem_insert_iff.1 hb with h2 | h2
    · rw [h1, h2]
    · rw [h1]
      exact (hx b h2).symm
  · rcases Set.mem_insert_iff.1 hb with h2 | h2
    · rw [h2]
      exact hx a h1
    · exact hZ.1 a h1 b h2

theorem cx_comm (hZ : CR Z) (hx : x ∈ Bz Z) : ∀ a ∈ Cx Z x, ∀ b ∈ Cx Z x, a * b = b * a := by
  intro a ha b hb
  have key := cx_gens hZ hx
  have h : Commute a b := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
    intro c hc
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_).symm
    intro d hd
    exact key c hc d hd
  exact h.eq

theorem z_le_cx : Z ≤ Cx Z x := fun _ h => Algebra.subset_adjoin (Set.mem_insert_of_mem _ h)

theorem x_mem_cx : x ∈ Cx Z x := Algebra.subset_adjoin (Set.mem_insert _ _)

theorem pe_mem {d : ℕ} {c : Fin d → Matrix (Fin N) (Fin N) k} (hc : ∀ l, c l ∈ Z) : pe c x ∈ Cx Z x :=
  Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ (z_le_cx (hc l)) (Subalgebra.pow_mem _ x_mem_cx _)

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k}

def Nx (x : Matrix (Fin N) (Fin N) k) : Submodule k (Matrix (Fin N) (Fin N) k) :=
  (Cx Z x).toSubmodule.map (LinearMap.mulLeft k (pe D.b x))

theorem s_mem (j : Fin D.r) : pe (D.a j) x ∈ Sx D x := Algebra.subset_adjoin ⟨j, rfl⟩

theorem sx_le : Sx D x ≤ Cx Z x := Algebra.adjoin_le (by rintro _ ⟨j, rfl⟩; exact pe_mem (D.ha j))

theorem sx_toSub (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    (Sx D x).toSubmodule = Submodule.span k (Set.range fun j => pe (D.a j) x) := by
  obtain ⟨h1, h2, -⟩ := D.spec x hx hχ
  apply le_antisymm
  · let P : Subalgebra k (Matrix (Fin N) (Fin N) k) :=
      (Submodule.span k (Set.range fun j => pe (D.a j) x)).toSubalgebra ?one ?mul
    · have hle : Sx D x ≤ P := by
        refine Algebra.adjoin_le ?_
        intro y hy
        exact Submodule.subset_span hy
      intro y hy
      exact hle hy
    case one =>
      rw [← h2]
      refine Submodule.sum_mem _ ?_
      intro j _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    case mul =>
      intro a b ha hb
      have hab : a * b ∈ Submodule.span k (Set.range fun j => pe (D.a j) x) *
          Submodule.span k (Set.range fun j => pe (D.a j) x) := Submodule.mul_mem_mul ha hb
      rw [Submodule.span_mul_span] at hab
      refine (Submodule.span_le.2 ?_) hab
      rintro _ ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩
      have e := h1 i j
      simp only at e ⊢
      rw [e]
      refine Submodule.sum_mem _ ?_
      intro t _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · refine Submodule.span_le.2 ?_
    intro y hy
    exact Algebra.subset_adjoin hy

theorem sx_nil (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : ∀ y ∈ Sx D x, IsNilpotent y → y = 0 := by
  obtain ⟨-, -, -, -, -, hred, -⟩ := D.spec x hx hχ
  intro y hy hn
  have : y ∈ (Sx D x).toSubmodule := hy
  rw [sx_toSub D hx hχ] at this
  exact hred y this hn

theorem sx_cr (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : CR (Sx D x) := by
  refine ⟨fun a ha b hb => cx_comm hZ hx a (sx_le D ha) b (sx_le D hb), ⟨fun y hy => ?_⟩⟩
  exact Subtype.ext (sx_nil D hx hχ y.1 y.2 (hy.map (Sx D x).val))

theorem nx_le : Nx D x ≤ (Cx Z x).toSubmodule := by
  refine Submodule.map_le_iff_le_comap.2 ?_
  intro y hy
  rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
  exact (Cx Z x).mul_mem (pe_mem D.hb) hy

theorem nx_nil (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : ∀ n ∈ Nx D x, IsNilpotent n := by
  obtain ⟨-, -, -, -, hεq, -⟩ := D.spec x hx hχ
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨q, ?_⟩
  simp only [LinearMap.mulLeft_apply]
  rw [(Commute.mul_pow (cx_comm hZ hx _ (pe_mem D.hb) c hc) q), hεq, zero_mul]

theorem nx_mul (hZ : CR Z) (hx : x ∈ Bz Z) : ∀ c ∈ Cx Z x, ∀ n ∈ Nx D x, c * n ∈ Nx D x := by
  intro c hc n hn
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hn
  refine Submodule.mem_map.2 ⟨c * y, (Cx Z x).mul_mem hc hy, ?_⟩
  rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc, ← mul_assoc,
    cx_comm hZ hx _ hc _ (pe_mem D.hb)]

theorem re_mem (hZ : CR Z) (hx : x ∈ Bz Z) (γ' : Fin D.d → Fin D.r → k) :
    re γ' (fun j => pe (D.a j) x) (pe D.b x) ∈ (Sx D x).toSubmodule ⊔ Nx D x := by
  simp only [re]
  refine Submodule.sum_mem _ ?_
  intro l _
  refine Submodule.sum_mem _ ?_
  intro j _
  refine Submodule.smul_mem _ _ ?_
  obtain h | ⟨m, hm⟩ : (l : ℕ) = 0 ∨ ∃ m, (l : ℕ) = m + 1 := by
    rcases (l : ℕ) with _ | m
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [h, pow_zero, mul_one]
    exact Submodule.mem_sup_left (s_mem D j)
  · have hs : pe (D.a j) x ∈ Cx Z x := pe_mem (D.ha j)
    have he : pe D.b x ∈ Cx Z x := pe_mem D.hb
    rw [hm, pow_succ', ← mul_assoc, cx_comm hZ hx _ hs _ he, mul_assoc]
    refine Submodule.mem_sup_right (Submodule.mem_map.2 ⟨pe (D.a j) x * pe D.b x ^ m, ?_, ?_⟩)
    · exact (Cx Z x).mul_mem hs ((Cx Z x).pow_mem he m)
    · rw [LinearMap.mulLeft_apply]

theorem z_le (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : Z.toSubmodule ≤ (Sx D x).toSubmodule ⊔ Nx D x := by
  obtain ⟨-, -, -, -, -, -, hz, -⟩ := D.spec x hx hχ
  rw [D.hz]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  rw [hz i]
  exact re_mem D hZ hx (D.γ i)

theorem x_mem (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) : x ∈ (Sx D x).toSubmodule ⊔ Nx D x := by
  obtain ⟨-, -, -, -, -, -, -, hxb, -⟩ := D.spec x hx hχ
  have := re_mem D hZ hx D.β
  rwa [← hxb] at this

theorem idem_mem (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ Z)
    (hfi : IsIdempotentElem f) : f ∈ Sx D x := by
  have hfm : f ∈ (Sx D x).toSubmodule ⊔ Nx D x := z_le D hZ hx hχ hf
  obtain ⟨s, hs, n, hn, hsn⟩ := Submodule.mem_sup.1 hfm
  have hsS : s ∈ Sx D x := hs
  have hsC : s ∈ Cx Z x := sx_le D hsS
  have hnC : n ∈ Cx Z x := nx_le D hn
  have hfC : f ∈ Cx Z x := z_le_cx hf
  have hnn : IsNilpotent n := nx_nil D hZ hx hχ n hn
  have cfn : Commute f n := cx_comm hZ hx f hfC n hnC
  have cfs : Commute f s := cx_comm hZ hx f hfC s hsC
  have hs_eq : s = f - n := by rw [← hsn]; abel
  have key : s * s - s = n * (n + 1 - 2 * f) := by
    have e : (f - n) * (f - n) - (f - n) - n * (n + 1 - 2 * f) = (f * f - f) + (n * f - f * n) := by
      noncomm_ring
    rw [hfi.eq, cfn.eq, sub_self, sub_self, add_zero, sub_eq_zero] at e
    rw [hs_eq]
    exact e
  have c2 : Commute n (2 * f) := by
    rw [two_mul]
    exact cfn.symm.add_right cfn.symm
  have cn2 : Commute n (n + 1 - 2 * f) :=
    ((Commute.refl n).add_right (Commute.one_right n)).sub_right c2
  have hnil : IsNilpotent (s * s - s) := by
    rw [key]
    exact Commute.isNilpotent_mul_right cn2 hnn
  have hz : s * s - s = 0 :=
    sx_nil D hx hχ _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hsS hsS) hsS) hnil
  have hsi : IsIdempotentElem s := sub_eq_zero.1 hz
  have hfs : f - s = n := by rw [← hsn]; abel
  have hfeq : f = s :=
    eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute hfi hsi (by rw [hfs]; exact hnn) cfs
  rw [hfeq]
  exact hsS

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)}

theorem pi_orth (hA : CR A) {e e' : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) (he' : e' ∈ primIdem A) (h : e ≠ e') : e * e' = 0 := by
  obtain ⟨heA, hei, -, hep⟩ := he
  obtain ⟨heA', hei', -, hep'⟩ := he'
  have hc : e * e' = e' * e := hA.1 _ heA _ heA'
  have hm : e * e' ∈ A := A.mul_mem heA heA'
  have hi : IsIdempotentElem (e * e') := by
    unfold IsIdempotentElem
    calc e * e' * (e * e') = e * (e' * e) * e' := by simp only [mul_assoc]
      _ = e * e * (e' * e') := by rw [← hc]; simp only [mul_assoc]
      _ = e * e' := by rw [hei.eq, hei'.eq]
  have h1 : e * e' * e = e * e' := by rw [mul_assoc, ← hc, ← mul_assoc, hei.eq]
  have h2 : e * e' * e' = e * e' := by rw [mul_assoc, hei'.eq]
  rcases hep _ hm hi h1 with h3 | h3
  · exact h3
  rcases hep' _ hm hi h2 with h4 | h4
  · exact h4
  exact absurd (h3.symm.trans h4) h

theorem pi_field (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) {a : Matrix (Fin N) (Fin N) k} (ha : a ∈ A) : e * a = 0 ∨ ∃ b ∈ A, e * a * b = e := by
  obtain ⟨heA, hei, -, hep⟩ := he
  have hrA : e * a ∈ A := A.mul_mem heA ha
  letI iC : CommRing A := { (inferInstance : Ring A) with mul_comm := fun x y => Subtype.ext (hA.1 _ x.2 _ y.2) }
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  obtain ⟨n, z, hz⟩ := IsArtinian.exists_pow_succ_smul_dvd (⟨e * a, hrA⟩ : A) (1 : A)
  simp only [smul_eq_mul, mul_one] at hz

  set r := e * a with hr
  set w : Matrix (Fin N) (Fin N) k := (z : Matrix (Fin N) (Fin N) k) with hw
  have hwA : w ∈ A := z.2
  have hz' : r ^ (n + 1) * w = r ^ n := by
    have := congrArg Subtype.val hz
    simpa using this
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.1
  have hrw : r * w = w * r := hcomm _ hrA _ hwA

  have key : ∀ j, r ^ (n + 1) * (r * w) ^ j = r ^ (n + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ (r * w) j, ← mul_assoc, ih, ← mul_assoc, ← pow_succ, pow_succ' r (n + 1), mul_assoc, hz', ← pow_succ']
  set m := n + 1
  have hm : r ^ m = r ^ m * (r * w) ^ m := (key m).symm
  have hpow : (r * w) ^ m = r ^ m * w ^ m := (Commute.mul_pow hrw m)
  set f := r ^ m * w ^ m with hf
  have hfA : f ∈ A := A.mul_mem (A.pow_mem hrA _) (A.pow_mem hwA _)
  have hrm : r ^ m = r ^ m * f := by rw [← hpow]; exact hm
  have hfi : IsIdempotentElem f := by
    unfold IsIdempotentElem
    calc f * f = r ^ m * f * w ^ m := by
          rw [hf]
          have : w ^ m * (r ^ m * w ^ m) = r ^ m * w ^ m * w ^ m := by
            rw [← mul_assoc, hcomm _ (A.pow_mem hwA _) _ (A.pow_mem hrA _)]
          rw [mul_assoc, this]; simp only [mul_assoc]
      _ = f := by rw [← hrm]
  have hre : r * e = r := by rw [hr, mul_assoc, hcomm a ha e heA, ← mul_assoc, hei.eq]
  have hfe : f * e = f := by
    have : r ^ m * e = r ^ m := by
      rw [show m = n + 1 from rfl, pow_succ, mul_assoc, hre]
    rw [hf, mul_assoc, hcomm _ (A.pow_mem hwA _) e heA, ← mul_assoc, this]
  rcases hep f hfA hfi hfe with h0 | h1
  · left
    have : r ^ m = 0 := by rw [hrm, h0, mul_zero]
    have hnil : IsNilpotent (⟨r, hrA⟩ : A) := ⟨m, by ext1; simpa using this⟩
    have := hA.2.eq_zero _ hnil
    simpa using congrArg Subtype.val this
  · right
    refine ⟨r ^ n * w ^ m, A.mul_mem (A.pow_mem hrA _) (A.pow_mem hwA _), ?_⟩
    rw [← h1, hf, ← mul_assoc, ← pow_succ']

theorem pi_lin (hA : CR A) :
    LinearIndependent k (fun e : primIdem A => (e : Matrix (Fin N) (Fin N) k)) := by
  rw [linearIndependent_iff']
  intro s g hs i hi
  have hmul : (i : Matrix (Fin N) (Fin N) k) * ∑ j ∈ s, g j • (j : Matrix (Fin N) (Fin N) k) = g i • (i : Matrix (Fin N) (Fin N) k) := by
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · rw [mul_smul_comm, i.2.2.1.eq]
    · intro j _ hji
      rw [mul_smul_comm, pi_orth hA i.2 j.2 (fun h => hji (Subtype.ext h.symm)), smul_zero]
    · intro h; exact absurd hi h
  rw [hs, mul_zero] at hmul
  rcases smul_eq_zero.mp hmul.symm with h | h
  · exact h
  · exact absurd h i.2.2.2.1

theorem pi_fin (hA : CR A) : (primIdem A).Finite := by
  have := (pi_lin hA).finite
  exact Set.finite_coe_iff.mp this

theorem pi_below (hA : CR A) : ∀ (n : ℕ) (g : Matrix (Fin N) (Fin N) k), g.rank = n → g ∈ A → IsIdempotentElem g → g ≠ 0 →
    ∃ p ∈ primIdem A, p * g = p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hn hgA hgi hg0
  by_cases hprim : ∀ f ∈ A, IsIdempotentElem f → f * g = f → f = 0 ∨ f = g
  · exact ⟨g, ⟨hgA, hgi, hg0, hprim⟩, hgi.eq⟩
  push Not at hprim
  obtain ⟨h, hhA, hhi, hhg, hh0, hhg'⟩ := hprim
  have hgh : g * h = h := by rw [hA.1 _ hgA _ hhA, hhg]
  have hlt : h.rank < g.rank := by
    unfold Matrix.rank
    apply Submodule.finrank_lt_finrank_of_lt
    refine lt_of_le_of_ne ?_ ?_
    · rw [← hgh, Matrix.mulVecLin_mul]; exact LinearMap.range_comp_le_range _ _
    · intro heq
      apply hhg'
      have : ∀ v, h *ᵥ (g *ᵥ v) = g *ᵥ v := by
        intro v
        have hv : g *ᵥ v ∈ LinearMap.range h.mulVecLin := heq ▸ ⟨v, rfl⟩
        obtain ⟨u, hu⟩ := hv
        simp only [Matrix.mulVecLin_apply] at hu
        rw [← hu, Matrix.mulVec_mulVec, hhi.eq]
      have hhg2 : h * g = g := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, this v]
      rw [← hhg2, hhg]
  obtain ⟨p, hp, hph⟩ := ih _ (hn ▸ hlt) h rfl hhA hhi hh0
  refine ⟨p, hp, ?_⟩
  calc p * g = p * h * g := by rw [hph]
    _ = p * h := by rw [mul_assoc, hhg]
    _ = p := hph

theorem pi_sum (hA : CR A) : ∑ e ∈ (pi_fin hA).toFinset, e = 1 := by
  set s := ∑ e ∈ (pi_fin hA).toFinset, e with hs
  have hsA : s ∈ A := A.sum_mem fun e he => ((pi_fin hA).mem_toFinset.mp he).1
  have hps : ∀ p ∈ primIdem A, p * s = p := by
    intro p hp
    rw [hs, Finset.mul_sum, Finset.sum_eq_single p]
    · exact hp.2.1.eq
    · intro j hj hjp
      exact pi_orth hA hp ((pi_fin hA).mem_toFinset.mp hj) (Ne.symm hjp)
    · intro h; exact absurd ((pi_fin hA).mem_toFinset.mpr hp) h
  have hss : s * s = s := by
    rw [hs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    exact hps e ((pi_fin hA).mem_toFinset.mp he)
  by_contra hne
  have hu0 : 1 - s ≠ 0 := fun h => hne (sub_eq_zero.mp h).symm
  have hui : IsIdempotentElem (1 - s) := by
    unfold IsIdempotentElem
    rw [sub_mul, one_mul, mul_sub, mul_one, hss, sub_self, sub_zero]
  obtain ⟨p, hp, hpu⟩ := pi_below hA _ (1 - s) rfl (A.sub_mem A.one_mem hsA) hui hu0
  rw [mul_sub, mul_one, hps p hp, sub_self] at hpu
  exact hp.2.2.1 hpu.symm

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
include hZ hx hχ

theorem pz_mem_S {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ primIdem Z) : f ∈ Sx D x :=
  idem_mem D hZ hx hχ hf.1 hf.2.1

theorem ef_cases {e f : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z) :
    e * f = 0 ∨ e * f = e := by
  have hfS := pz_mem_S D hZ hx hχ hf
  have hc : f * e = e * f := (sx_cr D hZ hx hχ).1 f hfS e he.1
  apply he.2.2.2 (e * f) (Subalgebra.mul_mem _ he.1 hfS)
  · show e * f * (e * f) = e * f
    calc e * f * (e * f) = e * (f * e) * f := by simp only [mul_assoc]
      _ = e * (e * f) * f := by rw [hc]
      _ = (e * e) * (f * f) := by simp only [mul_assoc]
      _ = e * f := by rw [he.2.1.eq, hf.2.1.eq]
  · calc e * f * e = e * (f * e) := mul_assoc _ _ _
      _ = e * (e * f) := by rw [hc]
      _ = e * f := by rw [← mul_assoc, he.2.1.eq]

theorem ef_exists {e : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) : ∃ f ∈ primIdem Z, e * f = e := by
  by_contra hno
  push_neg at hno
  apply he.2.2.1
  have hsum := pi_sum hZ
  calc e = e * ∑ g ∈ (pi_fin hZ).toFinset, g := by rw [hsum, mul_one]
    _ = ∑ g ∈ (pi_fin hZ).toFinset, e * g := Finset.mul_sum _ _ _
    _ = ∑ g ∈ (pi_fin hZ).toFinset, (0 : Matrix (Fin N) (Fin N) k) := by
      refine Finset.sum_congr rfl ?_
      intro g hg
      have hg' : g ∈ primIdem Z := (Set.Finite.mem_toFinset _).1 hg
      rcases ef_cases D hZ hx hχ he hg' with h0 | h0
      · exact h0
      · exact absurd h0 (hno g hg')
    _ = 0 := Finset.sum_const_zero

theorem ef_unique {e f f' : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z)
    (hf' : f' ∈ primIdem Z) (hef : e * f = e) (hef' : e * f' = e) : f = f' := by
  by_contra hff
  have h0 := pi_orth hZ hf' hf (Ne.symm hff)
  apply he.2.2.1
  calc e = e * f := hef.symm
    _ = e * f' * f := by rw [hef']
    _ = e * (f' * f) := mul_assoc _ _ _
    _ = 0 := by rw [h0, mul_zero]

open Classical in
theorem fib_sum {f : Matrix (Fin N) (Fin N) k} (hf : f ∈ primIdem Z) :
    ∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset with e * f = e, e = f := by
  rw [Finset.sum_filter]
  have h1 := pi_sum (sx_cr D hZ hx hχ)
  calc (∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, if e * f = e then e else 0)
      = ∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, e * f := by
        refine Finset.sum_congr rfl ?_
        intro e he
        have he' : e ∈ primIdem (Sx D x) := (Set.Finite.mem_toFinset _).1 he
        split_ifs with h
        · exact h.symm
        · rcases ef_cases D hZ hx hχ he' hf with h0 | h0
          · exact h0.symm
          · exact absurd h0 h
    _ = (∑ e ∈ (pi_fin (sx_cr D hZ hx hχ)).toFinset, e) * f := (Finset.sum_mul _ _ _).symm
    _ = f := by rw [h1, one_mul]

def Tef (e f : Matrix (Fin N) (Fin N) k) : Submodule k (Matrix (Fin N) (Fin N) k) :=
  (Z.toSubmodule.map (LinearMap.mulLeft k f)).map (LinearMap.mulLeft k e)

omit hχ in
theorem tef_zero {e f : Matrix (Fin N) (Fin N) k} (heid : IsIdempotentElem e) (hne : e ≠ 0) (hf : f ∈ primIdem Z)
    (hef : e * f = e) (hC : e ∈ Cx Z x) {z : Matrix (Fin N) (Fin N) k} (hz : z ∈ Z) (hn : IsNilpotent (e * (f * z))) :
    f * z = 0 := by
  rcases pi_field hZ hf hz with h0 | ⟨b, hb, hfb⟩
  · exact h0
  · exfalso
    apply hne
    have hfzC : f * z ∈ Cx Z x := (Cx Z x).mul_mem (z_le_cx hf.1) (z_le_cx hz)
    have hefz : e * (f * z) ∈ Cx Z x := (Cx Z x).mul_mem hC hfzC
    have hcb : Commute (e * (f * z)) b := cx_comm hZ hx _ hefz b (z_le_cx hb)
    have hnb : IsNilpotent (e * (f * z) * b) := Commute.isNilpotent_mul_right hcb hn
    have heq : e * (f * z) * b = e := by
      rw [mul_assoc, hfb, hef]
    rw [heq] at hnb
    exact heid.eq_zero_of_isNilpotent hnb

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
  {e f : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z) (hef : e * f = e)
include hZ hx hχ he hf hef

theorem tef_nil {w : Matrix (Fin N) (Fin N) k} (hw : w ∈ Tef (Z := Z) e f) (hn : IsNilpotent w) : w = 0 := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  simp only [LinearMap.mulLeft_apply] at hn ⊢
  rw [tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz hn, mul_zero]

theorem tef_finrank : finrank k (Tef (Z := Z) e f) = finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) := by
  have hinj : Function.Injective ((LinearMap.mulLeft k e).comp
      (Submodule.subtype (Z.toSubmodule.map (LinearMap.mulLeft k f)))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, hy⟩ h0
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulLeft_apply] at h0
    have hfz := tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz (by rw [h0]; exact IsNilpotent.zero)
    apply Subtype.ext
    simpa using hfz
  have h := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

theorem tef_inf : Tef (Z := Z) e f ⊓ Nx D x = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  exact tef_nil D hZ hx hχ he hf hef hw.1 (nx_nil D hZ hx hχ w hw.2)

theorem tef_le : Tef (Z := Z) e f ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 (z_le D hZ hx hχ hz)
  simp only [LinearMap.mulLeft_apply]
  have hfS : f ∈ Sx D x := pz_mem_S D hZ hx hχ hf
  have hfC : f ∈ Cx Z x := z_le_cx hf.1
  have heC : e ∈ Cx Z x := sx_le D he.1
  have hs' : s ∈ Sx D x := (Subalgebra.mem_toSubmodule _).1 hs
  rw [mul_add, mul_add]
  refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨f * s, (Subalgebra.mem_toSubmodule _).2 ((Sx D x).mul_mem hfS hs'), rfl⟩) ?_
  rw [← mul_assoc]
  exact nx_mul D hZ hx (e * f) ((Cx Z x).mul_mem heC hfC) n hn

theorem dim_le : finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) ≤
    finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) := by
  rw [← tef_finrank D hZ hx hχ he hf hef]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  omega

theorem dim_eq_le (hd : finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) ≤
    finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ≤ Tef (Z := Z) e f ⊔ Nx D x := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero, tef_finrank D hZ hx hχ he hf hef] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  have h5 := Submodule.eq_of_le_of_finrank_le h2 (by omega)
  rw [h5]
  exact le_sup_left

end

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
include hZ hx hχ

theorem zn_of_eq (h : ∀ f ∈ primIdem Z, f ∈ primIdem (Sx D x) ∧
      finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k f)) ≤ finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hfin := pi_fin hZ
  have hS : (Sx D x).toSubmodule ≤ Z.toSubmodule ⊔ Nx D x := by
    intro s hs
    have hsum : s = ∑ f ∈ hfin.toFinset, f * s := by
      rw [← Finset.sum_mul, pi_sum hZ, one_mul]
    rw [hsum]
    refine Submodule.sum_mem _ (fun f hf => ?_)
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨hfS, hd⟩ := h f hf
    have hle := dim_eq_le D hZ hx hχ hfS hf hfS.2.1.eq hd
    have hmem : f * s ∈ (Sx D x).toSubmodule.map (LinearMap.mulLeft k f) :=
      Submodule.mem_map.2 ⟨s, hs, rfl⟩
    have hT : Tef (Z := Z) f f ≤ Z.toSubmodule ⊔ Nx D x := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      apply Submodule.mem_sup_left
      simp only [LinearMap.mulLeft_apply]
      exact (Subalgebra.mem_toSubmodule _).2 (Z.mul_mem hf.1 (Z.mul_mem hf.1 hz))
    exact (sup_le hT le_sup_right) (hle hmem)
  have hxm : x ∈ Z.toSubmodule ⊔ Nx D x :=
    (sup_le hS le_sup_right : (Sx D x).toSubmodule ⊔ Nx D x ≤ _) (x_mem D hZ hx hχ)
  obtain ⟨c, hc, n, hn, hcn⟩ := Submodule.mem_sup.1 hxm
  refine ⟨c, hc, ?_⟩
  rw [← hcn, add_sub_cancel_left]
  exact nx_nil D hZ hx hχ n hn

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ}

abbrev Wd (e : Matrix (Fin N) (Fin N) k) : Submodule k (Fin N → k) := LinearMap.range e.mulVecLin

lemma mat_ext {b b' : Matrix (Fin N) (Fin N) k} (h : ∀ v, b *ᵥ v = b' *ᵥ v) : b = b' :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)

lemma toMatrix'_mulVec' (f : (Fin N → k) →ₗ[k] (Fin N → k)) (v : Fin N → k) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

lemma W_fix {e : Matrix (Fin N) (Fin N) k} (hid : IsIdempotentElem e) {w : Fin N → k} (hw : w ∈ Wd e) :
    e *ᵥ w = w := by
  obtain ⟨v, rfl⟩ := hw
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hid.eq]

lemma W_stable {e a : Matrix (Fin N) (Fin N) k} (hc : a * e = e * a) {w : Fin N → k} (hw : w ∈ Wd e) :
    a *ᵥ w ∈ Wd e := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨a *ᵥ v, by simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hc]⟩

variable {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

def rho (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) : A →ₐ[k] Module.End k (Wd e) where
  toFun a := (a.1.mulVecLin).restrict (fun w hw => W_stable (hA _ a.2 _ he) hw)
  map_one' := by ext w; simp
  map_mul' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 * b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (b.1 *ᵥ (w : Fin N → k))
    rw [Matrix.mulVec_mulVec]
  map_zero' := by ext w; simp
  map_add' a b := by
    ext w : 1; apply Subtype.ext
    show (a.1 + b.1) *ᵥ (w : Fin N → k) = a.1 *ᵥ (w : Fin N → k) + b.1 *ᵥ (w : Fin N → k)
    rw [Matrix.add_mulVec]
  commutes' r := by ext w; simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]

lemma rho_apply (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A) (a : A) (w : Wd e) :
    ((rho hA he a w : Wd e) : Fin N → k) = a.1 *ᵥ (w : Fin N → k) := rfl

abbrev Pe (e : Matrix (Fin N) (Fin N) k) : (Fin N → k) →ₗ[k] Wd e := LinearMap.rangeRestrict e.mulVecLin

lemma Pe_surj (e : Matrix (Fin N) (Fin N) k) : Function.Surjective (Pe e) := LinearMap.surjective_rangeRestrict _

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}

def Th (e : Matrix (Fin N) (Fin N) k) : Module.End k (Wd e) →ₗ[k] Matrix (Fin N) (Fin N) k where
  toFun f := LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e)
  map_add' f g := by rw [← map_add]; congr 1
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; congr 1

lemma Th_mulVec (f : Module.End k (Wd e)) (v : Fin N → k) : Th e f *ᵥ v = (f (Pe e v) : Fin N → k) := by
  show LinearMap.toMatrix' ((Wd e).subtype ∘ₗ f ∘ₗ Pe e) *ᵥ v = _
  exact toMatrix'_mulVec' _ v

lemma Th_inj : Function.Injective (Th (k := k) (N := N) e) := by
  intro f g h
  ext w : 1
  obtain ⟨v, rfl⟩ := Pe_surj e w
  have := congrArg (· *ᵥ v) h
  simp only [Th_mulVec] at this
  exact Subtype.ext this

variable (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

lemma Th_rho (a : A) : Th e (rho hA he a) = e * a.1 := by
  apply mat_ext; intro v
  rw [Th_mulVec, rho_apply]
  simp [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hA _ a.2 _ he]

abbrev Fe : Subalgebra k (Module.End k (Wd e)) := (rho hA he).range

lemma map_Th_Fe : (Fe hA he).toSubmodule.map (Th e) = A.toSubmodule.map (LinearMap.mulLeft k e) := by
  ext m; constructor
  · rintro ⟨f, ⟨a, rfl⟩, rfl⟩
    exact ⟨a.1, a.2, by simp [Th_rho hA he]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨rho hA he ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, by simp [Th_rho hA he]⟩

lemma Fe_isField (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) : IsField (Fe hA he) := by
  have hW : ∃ v : Fin N → k, e *ᵥ v ≠ 0 := by
    by_contra h; push Not at h; exact hne (mat_ext fun v => by simp [h v])
  obtain ⟨v₀, hv₀⟩ := hW
  refine ⟨⟨0, 1, fun h => ?_⟩, ?_, ?_⟩
  · have := congrArg (fun x : Fe hA he => ((x.1 (Pe e v₀) : Wd e) : Fin N → k)) h
    change 0 = e *ᵥ v₀ at this
    exact hv₀ this.symm
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show rho hA he a * rho hA he b = rho hA he b * rho hA he a
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA _ a.2 _ b.2)
  · rintro ⟨_, a, rfl⟩ hx
    have hea : e * a.1 ≠ 0 := by
      intro h0; apply hx; apply Subtype.ext
      ext w : 1; apply Subtype.ext
      obtain ⟨v, rfl⟩ := Pe_surj e w
      show a.1 *ᵥ (e *ᵥ v) = 0
      rw [Matrix.mulVec_mulVec, hA _ a.2 _ he, h0, Matrix.zero_mulVec]
    rcases hf a.1 a.2 with h0 | ⟨b, hb, hab⟩
    · exact absurd h0 hea
    refine ⟨⟨rho hA he ⟨b, hb⟩, ⟨b, hb⟩, rfl⟩, ?_⟩
    apply Subtype.ext
    ext w : 1; apply Subtype.ext
    obtain ⟨v, rfl⟩ := Pe_surj e w
    show a.1 *ᵥ (b *ᵥ (e *ᵥ v)) = e *ᵥ v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, hA _ hb _ he, ← mul_assoc,
      hA _ a.2 _ he, hab]

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

variable {k : Type} [Field k] {N : ℕ} {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} {e : Matrix (Fin N) (Fin N) k}
  (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (he : e ∈ A)

instance Fe_tower : IsScalarTower k (Fe hA he) (Wd e) := ⟨fun _ _ _ => rfl⟩

def Psi : Module.End (Fe hA he) (Wd e) →ₗ[k] Matrix (Fin N) (Fin N) k where
  toFun φ := Th e (φ.restrictScalars k)
  map_add' f g := by rw [← map_add]; rfl
  map_smul' c f := by rw [RingHom.id_apply, ← map_smul]; rfl

lemma Psi_mulVec (φ : Module.End (Fe hA he) (Wd e)) (v : Fin N → k) :
    Psi hA he φ *ᵥ v = (φ (Pe e v) : Fin N → k) := Th_mulVec (φ.restrictScalars k) v

lemma Psi_inj : Function.Injective (Psi hA he) := by
  intro f g h
  have := Th_inj h
  ext w : 1
  exact congrArg (fun F : Module.End k (Wd e) => F w) this

lemma Pe_smul (a : A) (v : Fin N → k) :
    Pe e (a.1 *ᵥ v) = (⟨rho hA he a, a, rfl⟩ : Fe hA he) • Pe e v := by
  apply Subtype.ext
  show e *ᵥ (a.1 *ᵥ v) = a.1 *ᵥ (e *ᵥ v)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA _ a.2 _ he]

def phiOf (c : Matrix (Fin N) (Fin N) k) (hc : ∀ a ∈ A, a * c = c * a) : Module.End (Fe hA he) (Wd e) where
  toFun w := ⟨c *ᵥ (w : Fin N → k), W_stable (hc e he).symm w.2⟩
  map_add' w w' := by apply Subtype.ext; exact Matrix.mulVec_add c w.1 w'.1
  map_smul' := by
    rintro ⟨_, a, rfl⟩ w
    apply Subtype.ext
    show c *ᵥ (a.1 *ᵥ (w : Fin N → k)) = a.1 *ᵥ (c *ᵥ (w : Fin N → k))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc _ a.2]

lemma range_Psi (hid : IsIdempotentElem e) :
    LinearMap.range (Psi hA he) =
      (Subalgebra.centralizer k (A : Set (Matrix (Fin N) (Fin N) k))).toSubmodule.map (LinearMap.mulLeft k e) := by
  ext m; constructor
  · rintro ⟨φ, rfl⟩
    refine ⟨Psi hA he φ, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
      intro a ha
      apply mat_ext; intro v
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Psi_mulVec, Psi_mulVec,
        Pe_smul hA he ⟨a, ha⟩, map_smul]
      rfl
    · apply mat_ext; intro v
      simp only [LinearMap.mulLeft_apply]
      rw [← Matrix.mulVec_mulVec, Psi_mulVec]
      exact W_fix hid (φ (Pe e v)).2
  · rintro ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at hc
    refine ⟨phiOf hA he c hc, ?_⟩
    apply mat_ext; intro v
    rw [Psi_mulVec]
    show c *ᵥ (e *ᵥ v) = (e * c) *ᵥ v
    rw [Matrix.mulVec_mulVec, hc e he]

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem pi_ratio {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {e : Matrix (Fin N) (Fin N) k} (he : e ∈ A) (hid : IsIdempotentElem e) (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) :
    0 < Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) ∧
      Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) ∣ e.rank ∧
      Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) =
        (e.rank / Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))) ^ 2 *
          Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) := by
  classical
  let _ : Field (Fe hA he) := (Fe_isField hA he hne hf).toField
  have hFd : Module.finrank k (Fe hA he) = Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) := by
    rw [← map_Th_Fe hA he, ← (Submodule.equivMapOfInjective (Th e) Th_inj _).finrank_eq,
      Subalgebra.finrank_toSubmodule]
  have hD : Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) =
      Module.finrank k (Module.End (Fe hA he) (Wd e)) := by
    unfold cenSub
    rw [← range_Psi hA he hid, LinearMap.finrank_range_of_inj (Psi_inj hA he)]
  have h1 := GroundTheory.Brauer.finrank_mul_finrank_end k (Fe hA he) (Wd e)
  have h2 := Module.finrank_mul_finrank k (Fe hA he) (Wd e)
  have hr : e.rank = Module.finrank k (Wd e) := rfl
  have hd0 : 0 < Module.finrank k (Fe hA he) := Module.finrank_pos
  rw [← hFd, hD, hr]
  set d := Module.finrank k (Fe hA he)
  set m := Module.finrank (Fe hA he) (Wd e)
  rw [← h2] at h1 ⊢
  refine ⟨hd0, dvd_mul_right _ _, ?_⟩
  rw [Nat.mul_div_cancel_left m hd0]
  apply Nat.eq_of_mul_eq_mul_left hd0
  rw [h1]; ring

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open Matrix

variable {k : Type} [Field k] {N : ℕ}

theorem rank_add_orth {a b : Matrix (Fin N) (Fin N) k} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b = 0) (hba : b * a = 0) : (a + b).rank = a.rank + b.rank := by
  have hsup : LinearMap.range (a + b).mulVecLin = LinearMap.range a.mulVecLin ⊔ LinearMap.range b.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, rfl⟩
        refine ⟨a *ᵥ v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, ha.eq, hba, add_zero]
      · rintro _ ⟨v, rfl⟩
        refine ⟨b *ᵥ v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hb.eq, hab, zero_add]
  have hinf : LinearMap.range a.mulVecLin ⊓ LinearMap.range b.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    simp only [Matrix.mulVecLin_apply] at hv ⊢
    have h1 : a *ᵥ (a *ᵥ u) = a *ᵥ u := by rw [Matrix.mulVec_mulVec, ha.eq]
    have h2 : a *ᵥ (b *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, hab, Matrix.zero_mulVec]
    rw [← hv, h2] at h1
    rw [Submodule.mem_bot, ← hv, ← h1]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range a.mulVecLin) (LinearMap.range b.mulVecLin)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  exact h

theorem idem_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    IsIdempotentElem (∑ i ∈ s, e i) := by
  unfold IsIdempotentElem
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => ho i hi j hj (Ne.symm hji)) (fun h => absurd hi h)]
  exact hid i hi

theorem rank_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    (∑ i ∈ s, e i).rank = ∑ i ∈ s, (e i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hid' : ∀ j ∈ s, IsIdempotentElem (e j) := fun j hj => hid j (Finset.mem_insert_of_mem hj)
    have ho' : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → e j * e l = 0 := fun j hj l hl h =>
      ho j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) h
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih hid' ho']
    refine rank_add_orth (hid i (Finset.mem_insert_self i s)) (idem_sum_orth s e hid' ho') ?_ ?_
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => ho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    · rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun j hj => ho j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)
        (fun h => hi (h ▸ hj))

theorem rank_pos_of_ne {e : Matrix (Fin N) (Fin N) k} (h : e ≠ 0) : 0 < e.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [Matrix.rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have : Matrix.toLin' e = 0 := h0
  simpa using congrArg LinearMap.toMatrix' this

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end

section
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

theorem sq_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) : ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith [ih, Nat.zero_le (m a * ∑ i ∈ s, m i)]

theorem sq_sum_lt {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) (h : 1 < s.card) :
    ∑ i ∈ s, m i ^ 2 < (∑ i ∈ s, m i) ^ 2 := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have hne : (s.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := hne
  have hM : 1 ≤ ∑ i ∈ s.erase a, m i :=
    (hm b (Finset.mem_of_mem_erase hb)).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)
  have ih := sq_sum_le (s.erase a) m
  rw [← Finset.add_sum_erase s _ ha, ← Finset.add_sum_erase s _ ha]
  have := hm a ha
  nlinarith

theorem num_fib {ι : Type*} [DecidableEq ι] (s : Finset ι) (m dE : ι → ℕ) (n dF : ℕ) (hdF : 0 < dF)
    (hm : ∀ i ∈ s, 1 ≤ m i) (hd : ∀ i ∈ s, dF ≤ dE i) (hsum : n * dF = ∑ i ∈ s, m i * dE i) :
    ∑ i ∈ s, m i ^ 2 ≤ n ^ 2 ∧ (∑ i ∈ s, m i ^ 2 = n ^ 2 → s.Nonempty → ∀ i ∈ s, s = {i} ∧ dE i ≤ dF) := by
  have hMn : ∑ i ∈ s, m i ≤ n := by
    have : (∑ i ∈ s, m i) * dF ≤ n * dF := by
      rw [hsum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (hd i hi)
    exact Nat.le_of_mul_le_mul_right this hdF
  have h1 := sq_sum_le s m
  have h2 : (∑ i ∈ s, m i) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hMn 2
  refine ⟨h1.trans h2, fun heq hne i hi => ?_⟩
  have hcard : s.card = 1 := by
    by_contra hc
    have := sq_sum_lt s m hm (by have := hne.card_pos; omega)
    omega
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.mem_singleton] at hi; subst hi
  refine ⟨rfl, ?_⟩
  simp only [Finset.sum_singleton] at heq hsum
  have hn : m i = n := by
    have := (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) heq
    exact this
  rw [← hn] at hsum
  have := hm i (Finset.mem_singleton_self i)
  have : dF = dE i := Nat.eq_of_mul_eq_mul_left (by omega) hsum
  omega

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

abbrev dA (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (e : Matrix (Fin N) (Fin N) k) : ℕ :=
  finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))

theorem ratio_of (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) :
    0 < dA A e ∧ dA A e ∣ e.rank ∧
      finrank k ((cenSub A).map (LinearMap.mulLeft k e)) / dA A e = (e.rank / dA A e) ^ 2 := by
  obtain ⟨h0, hd, h⟩ := pi_ratio hA.1 he.1 he.2.1 he.2.2.1 (fun a ha => pi_field hA he ha)
  exact ⟨h0, hd, by rw [h, Nat.mul_div_cancel _ h0]⟩

theorem mu_sum (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) :
    mu A = ∑ e ∈ (pi_fin hA).toFinset, (e.rank / dA A e) ^ 2 := by
  unfold mu
  rw [finsum_mem_eq_finite_toFinset_sum _ (pi_fin hA)]
  exact Finset.sum_congr rfl fun e he => (ratio_of A hA ((Set.Finite.mem_toFinset _).mp he)).2.2

theorem m_pos (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) : 1 ≤ e.rank / dA A e := by
  obtain ⟨h0, hd, -⟩ := ratio_of A hA he
  have hr := rank_pos_of_ne he.2.2.1
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.mul_div_cancel_left _ h0]
  rcases Nat.eq_zero_or_pos c with rfl | h
  · simp at hc; omega
  · exact h

open Classical in
theorem dich_pt {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
    {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    mu (Sx D x) < mu Z ∨ ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hS := sx_cr D hZ hx hχ
  set P := (pi_fin hS).toFinset with hP
  set Q := (pi_fin hZ).toFinset with hQ
  have mP : ∀ {e}, e ∈ P ↔ e ∈ primIdem (Sx D x) := fun {e} => Set.Finite.mem_toFinset _
  have mQ : ∀ {f}, f ∈ Q ↔ f ∈ primIdem Z := fun {f} => Set.Finite.mem_toFinset _

  have hsplit : mu (Sx D x) = ∑ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 := by
    rw [mu_sum _ hS]
    calc ∑ e ∈ P, (e.rank / dA (Sx D x) e) ^ 2
        = ∑ e ∈ P, ∑ f ∈ Q, if e * f = e then (e.rank / dA (Sx D x) e) ^ 2 else 0 := by
          refine Finset.sum_congr rfl fun e he => ?_
          obtain ⟨f₀, hf₀, hef₀⟩ := ef_exists D hZ hx hχ (mP.mp he)
          rw [Finset.sum_eq_single_of_mem f₀ (mQ.mpr hf₀) fun f hf hne => if_neg fun h =>
            hne (ef_unique D hZ hx hχ (mP.mp he) (mQ.mp hf) hf₀ h hef₀), if_pos hef₀]
      _ = ∑ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun f _ => (Finset.sum_filter _ _).symm

  have hfib : ∀ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 ≤ (f.rank / dA Z f) ^ 2 ∧
      (∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 = (f.rank / dA Z f) ^ 2 →
        f ∈ primIdem (Sx D x) ∧ dA (Sx D x) f ≤ dA Z f) := by
    intro f hf
    have hf' := mQ.mp hf
    have hmem : ∀ e ∈ P.filter (fun e => e * f = e), e ∈ primIdem (Sx D x) ∧ e * f = e := fun e he =>
      ⟨mP.mp (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
    have hfs := fib_sum D hZ hx hχ hf'
    obtain ⟨hdF, hdvF, -⟩ := ratio_of Z hZ hf'
    have hsum : f.rank / dA Z f * dA Z f =
        ∑ e ∈ P with e * f = e, e.rank / dA (Sx D x) e * dA (Sx D x) e := by
      rw [Nat.div_mul_cancel hdvF]
      conv_lhs => rw [← hfs]
      rw [rank_sum_orth _ _ (fun e he => (hmem e he).1.2.1)
        (fun e he e' he' hne => pi_orth hS (hmem e he).1 (hmem e' he').1 hne)]
      exact Finset.sum_congr rfl fun e he => (Nat.div_mul_cancel (ratio_of _ hS (hmem e he).1).2.1).symm
    obtain ⟨hle, heq⟩ := num_fib (P.filter (fun e => e * f = e)) (fun e => e.rank / dA (Sx D x) e)
      (fun e => dA (Sx D x) e) (f.rank / dA Z f) (dA Z f) hdF (fun e he => m_pos _ hS (hmem e he).1)
      (fun e he => dim_le D hZ hx hχ (hmem e he).1 hf' (hmem e he).2) hsum
    refine ⟨hle, fun h => ?_⟩
    have hne : (P.filter (fun e => e * f = e)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hfs
      exact hf'.2.2.1 hfs.symm
    obtain ⟨e, he⟩ := hne
    obtain ⟨hsing, hde⟩ := heq h ⟨e, he⟩ e he
    have hef : e = f := by rw [← hfs, hsing, Finset.sum_singleton]
    subst hef
    exact ⟨(hmem e he).1, hde⟩

  have hle : mu (Sx D x) ≤ mu Z := by
    rw [hsplit, mu_sum _ hZ]
    exact Finset.sum_le_sum fun f hf => (hfib f hf).1
  by_cases hlt : mu (Sx D x) < mu Z
  · exact Or.inl hlt
  right
  have heq : mu (Sx D x) = mu Z := le_antisymm hle (not_lt.mp hlt)
  rw [hsplit, mu_sum _ hZ] at heq
  have hall := (Finset.sum_eq_sum_iff_of_le fun f hf => (hfib f hf).1).mp heq
  exact zn_of_eq D hZ hx hχ fun f hf => (hfib f (mQ.mpr hf)).2 (hall f (mQ.mpr hf))

variable (k) in
theorem dich : PositivityTheory.RgUd.TP.Desc.Piece.Dich k := by
  intro N q Z hZ χ D τ x₀ hx₀
  exact dich_pt D hZ hx₀.1 hx₀.2.1

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

section
namespace PositivityTheory.RgUd.TP.Desc.Piece.Final

open PositivityTheory.RgUd.TP.Desc

theorem pieceGood (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PieceGood k :=
  PositivityTheory.RgUd.TP.Desc.Piece.PAsm2.pieceGood_of k PositivityTheory.PfBern.Frob.frobeniusReciprocity (PositivityTheory.RgUd.TP.Desc.Piece.PSect.sect k)
    (PositivityTheory.RgUd.TP.Desc.Piece.PTop.pieceTop k) (PositivityTheory.RgUd.TP.Desc.Piece.PDich.dich k)
    (PositivityTheory.RgUd.TP.Desc.Piece.PTr.transfer k)

end PositivityTheory.RgUd.TP.Desc.Piece.Final
end
