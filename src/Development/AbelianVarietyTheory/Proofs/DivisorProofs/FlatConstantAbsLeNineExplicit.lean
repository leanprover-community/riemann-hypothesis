import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodWeightAntitoneGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSetsStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortIndependentIntegers

section
section
set_option autoImplicit false

noncomputable section

open NumberField Module

namespace GlobalTheory

theorem exists_isShortGen_of_short_span : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ)
    (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) →
    (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L →
    Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) →
    ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧
      abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
        |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧
      n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  intro K V _ _ _ _ _ _ _ N L s A hLfg h0 hsm hadd hsL hsp hA
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ K)
  haveI : IsScalarTower ℚ K V := ⟨fun q a x => by
    show (q • a) • x = (algebraMap ℚ K q) • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have hspL : Submodule.span K (L : Set V) = ⊤ := eq_top_iff.2 (hsp ▸ Submodule.span_mono hsL)
  have hrk : Formalism.HN.rkK L = Module.finrank K V := by
    rw [Formalism.HN.rkK, hspL, finrank_top]

  obtain ⟨t, hts, htsp, hti⟩ := exists_linearIndependent K s
  let vb : Basis t K V := Basis.mk hti (by rw [Subtype.range_coe, htsp, hsp])
  haveI : Finite t := Module.Finite.finite_basis vb
  haveI : Fintype t := Fintype.ofFinite t
  have hm : Fintype.card t = Formalism.HN.rkK L := by rw [hrk, finrank_eq_card_basis vb]

  obtain ⟨ω, hωi, hωb⟩ := exists_short_independent_integers K
  haveI : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, Module.finrank_pos⟩⟩
  let ob : Basis (Fin (finrank ℚ K)) ℚ K := basisOfLinearIndependentOfCardEqFinrank hωi (by simp)
  have hob : ∀ k, ob k = (ω k : K) := fun k => by
    simp [ob, coe_basisOfLinearIndependentOfCardEqFinrank]
  let E : Basis (Fin (finrank ℚ K) × t) ℚ V := ob.smulTower vb
  have hE : ∀ p, E p = ω p.1 • (p.2 : V) := fun p => by
    rw [Basis.smulTower_apply, hob, Basis.mk_apply]
    exact algebraMap_smul K (ω p.1) (p.2 : V)

  have hN0 : ∀ σ, N σ 0 = 0 := fun σ => by simpa using hsm σ 0 0
  have hsum : ∀ σ {ι : Type} (S : Finset ι) (f : ι → V), N σ (∑ i ∈ S, f i) ≤ ∑ i ∈ S, N σ (f i) := by
    intro σ ι S f
    induction S using Finset.induction_on with
    | empty => simp [hN0]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (hadd σ _ _).trans (add_le_add le_rfl ih)
  have hq : ∀ σ (q : ℚ) x, N σ (q • x) = |(q : ℝ)| * N σ x := fun σ q x => by
    have := hsm σ (algebraMap ℚ K q) x
    rw [eq_ratCast, map_ratCast, Complex.norm_ratCast] at this
    exact this

  set C : ℝ := (finrank ℚ K : ℝ) ^ 3 * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A with hC
  have hEle : ∀ σ p, N σ (E p) ≤ C := fun σ p => by
    rw [hE p, ← algebraMap_smul K (ω p.1) (p.2 : V), hsm]
    have h1 := hA _ (hts p.2.2) σ
    exact mul_le_mul (hωb σ p.1) h1 (h0 _ _) ((norm_nonneg _).trans (hωb σ p.1))

  let red : V → V := fun x => ∑ p, Int.fract (E.repr x p) • E p
  have hred_sub : ∀ x, x - red x ∈ Submodule.span ℤ (Set.range E) := fun x => by
    have hx : x - red x = ∑ p, (⌊E.repr x p⌋ : ℤ) • E p := by
      rw [sub_eq_iff_eq_add, ← Finset.sum_add_distrib]
      conv_lhs => rw [← E.sum_repr x]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℚ, ← add_smul, Int.floor_add_fract]
    rw [hx]
    exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
  have hred_le : ∀ σ x, N σ (red x) ≤ ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C := fun σ x => by
    refine (hsum σ _ _).trans ?_
    have hle : ∀ p ∈ (Finset.univ : Finset (Fin (finrank ℚ K) × t)),
        N σ (Int.fract (E.repr x p) • E p) ≤ C := fun p _ => by
      rw [hq]
      have h1 : |((Int.fract (E.repr x p) : ℚ) : ℝ)| ≤ 1 := by
        rw [abs_of_nonneg (Rat.cast_nonneg.2 (Int.fract_nonneg _))]
        exact_mod_cast (Int.fract_lt_one _).le
      exact (mul_le_of_le_one_left (h0 _ _) h1).trans (hEle σ p)
    refine (Finset.sum_le_card_nsmul _ _ _ hle).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hm]
    push_cast; ring

  haveI : NoZeroSMulDivisors ℤ V := ⟨fun {c x} h => by
    rw [← Int.cast_smul_eq_zsmul K] at h
    exact (smul_eq_zero.1 h).imp_left Int.cast_eq_zero.1⟩
  let Lz := L.restrictScalars ℤ
  haveI : Module.Finite ℤ Lz := Module.Finite.iff_fg.2 hLfg.restrictScalars
  haveI : Module.Free ℤ Lz := Module.free_of_finite_type_torsion_free'
  let ZB := Module.Free.chooseBasis ℤ Lz
  let bZ : Module.Free.ChooseBasisIndex ℤ Lz → V := fun j => (ZB j : V)
  have hZq : LinearIndependent ℚ bZ := (LinearIndependent.iff_fractionRing ℤ ℚ).1
    (ZB.linearIndependent.map' Lz.subtype (Submodule.ker_subtype _))
  haveI : Module.Finite ℚ V := Module.Finite.of_basis E
  have hcardZ : Fintype.card (Module.Free.ChooseBasisIndex ℤ Lz) ≤ Fintype.card (Fin (finrank ℚ K) × t) := by
    rw [← finrank_eq_card_basis E]; exact hZq.fintype_card_le_finrank
  have hLz : Lz = Submodule.span ℤ (Set.range bZ) := by
    rw [show Set.range bZ = Lz.subtype '' Set.range ZB from Set.range_comp _ _, ← Submodule.map_span,
      ZB.span_eq, Submodule.map_top, Submodule.range_subtype]

  let F : (Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz → V := Sum.elim E (fun j => red (bZ j))
  let e := Fintype.equivFin ((Fin (finrank ℚ K) × t) ⊕ Module.Free.ChooseBasisIndex ℤ Lz)
  have hEL : ∀ p, E p ∈ L := fun p => by rw [hE]; exact L.smul_mem _ (hsL (hts p.2.2))
  have hspanE : Submodule.span ℤ (Set.range E) ≤ Lz :=
    Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hEL p)
  have hrng : Set.range (F ∘ e.symm) = Set.range F := e.symm.surjective.range_comp F
  have hbig : ((finrank ℚ K : ℝ) * Formalism.HN.rkK L) * C ≤ max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A) := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _); rw [hC]; ring
  refine ⟨Fintype.card _, F ∘ e.symm, max 1 ((finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) *
      |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (finrank ℚ K : ℝ)) * A),
    ⟨fun x => ?_, fun i σ => ?_, le_max_left _ _⟩, le_rfl, ?_⟩
  · rw [hrng]
    constructor
    · intro hx
      have hx' : x ∈ Lz := hx
      rw [hLz] at hx'
      refine (Submodule.span_le.2 ?_) hx'
      rintro _ ⟨j, rfl⟩
      have h1 : red (bZ j) ∈ Submodule.span ℤ (Set.range F) := Submodule.subset_span ⟨Sum.inr j, rfl⟩
      have h2 : bZ j - red (bZ j) ∈ Submodule.span ℤ (Set.range F) :=
        Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨Sum.inl p, rfl⟩) (hred_sub _)
      simpa using add_mem h2 h1
    · intro hx
      have : x ∈ Lz := (Submodule.span_le (p := Lz)).2 (by
        rintro _ ⟨q | j, rfl⟩
        · exact hEL q
        · have h1 : bZ j ∈ Lz := (ZB j).2
          have h2 := hspanE (hred_sub (bZ j))
          have e1 : red (bZ j) = bZ j - (bZ j - red (bZ j)) := by abel
          show red (bZ j) ∈ Lz
          rw [e1]; exact sub_mem h1 h2) hx
      exact this
  · refine le_trans ?_ hbig
    rw [Function.comp_apply]
    generalize e.symm i = q
    rcases q with q | j
    · have hC0 : 0 ≤ C := (h0 σ _).trans (hEle σ q)
      have hpos : 0 < Fintype.card t := Fintype.card_pos_iff.2 ⟨q.2⟩
      have h1 : (1 : ℝ) ≤ (finrank ℚ K : ℝ) * Formalism.HN.rkK L := by
        rw [← hm]
        exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero Module.finrank_pos.ne' hpos.ne')
      exact (hEle σ q).trans (le_mul_of_one_le_left hC0 h1)
    · exact hred_le σ _
  · rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, hm]
    rw [Fintype.card_prod, Fintype.card_fin, hm] at hcardZ
    linarith

end GlobalTheory
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_generators_of_short_spanning_family : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) → (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L → Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) → ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧ abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧ n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  atlas_forward_decl GlobalTheory.exists_isShortGen_of_short_span
end

section
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt

namespace GlobalTheory.PetAdd

theorem cnorm_add_le {ι : Type} [Fintype ι] (u w : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u + w) ≤ Formalism.HermitianLatticesTheory.cnorm u + Formalism.HermitianLatticesTheory.cnorm w := by
  have key : ∀ t : ι → ℂ, Formalism.HermitianLatticesTheory.cnorm t = ‖(WithLp.equiv 2 (ι → ℂ)).symm t‖ := fun t => by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [key, key, key]
  have e : (WithLp.equiv 2 (ι → ℂ)).symm (u + w) = (WithLp.equiv 2 (ι → ℂ)).symm u + (WithLp.equiv 2 (ι → ℂ)).symm w := by
    first | exact WithLp.equiv_symm_add 2 u w | rfl | simp
  rw [e]
  exact norm_add_le _ _

theorem IsGram.add_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {ι : Type} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (v : InfinitePlace K) (f g : V) :
    N v.embedding (f + g) ≤ N v.embedding f + N v.embedding g := by
  rw [← (h v).2, ← (h v).2, ← (h v).2]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  have : Formalism.HermitianLatticesTheory.vecAt b v (f + g) = Formalism.HermitianLatticesTheory.vecAt b v f + Formalism.HermitianLatticesTheory.vecAt b v g := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [this, Matrix.mulVec_add]
  exact cnorm_add_le _ _

end GlobalTheory.PetAdd

namespace GlobalTheory.PetAdd

theorem normOn_add_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), GoodOn U x V dict Z G → ∀ σ (f g : cuspOn U Z G), normOn U x V dict Z G σ (f + g) ≤ normOn U x V dict Z G σ f + normOn U x V dict Z G σ g := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G h σ f g
  obtain ⟨n, ⟨p, hp⟩⟩ := h.1
  have hconj : ∀ y, normOn U x V dict Z G ((starRingEnd ℂ).comp σ) y = normOn U x V dict Z G σ y :=
    fun y => GlobalTheory.CompHt.petOn_conj U x V dict Z G σ y
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    rwa [e] at this
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    have e' : (InfinitePlace.mk σ).embedding = (starRingEnd ℂ).comp σ := by
      rw [e]; ext a; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e', hconj, hconj, hconj] at this
    exact this

end GlobalTheory.PetAdd
end

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_norm_component_add_le_of_gramFrame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), GoodOn U x V dict Z G → ∀ σ (f g : cuspOn U Z G), normOn U x V dict Z G σ (f + g) ≤ normOn U x V dict Z G σ f + normOn U x V dict Z G σ g := by
  atlas_forward_decl GlobalTheory.PetAdd.normOn_add_le
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.ShortGenComp

set_option maxHeartbeats 1000000 in

theorem short_gen_comp : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 10 * Lb → ∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) (abelian₂ : ℝ), CompHt.IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) w abelian₂ ∧ Real.log abelian₂ ≤ C * (((D.R.f : ℝ) * D.R.r * Lb) ^ 3 * (∑ τ, ∑ k, |(la τ k : ℝ)|) + ((D.R.f : ℝ) * D.R.r * Lb) ^ 5) ∧ Real.log n ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  obtain ⟨C2, hC2, h2⟩ := GlobalTheory.T.flat_constant_abs_le_nine_deep hP
  obtain ⟨Cb, hCb, hb⟩ := GlobalTheory.T.antitone_weight_log_bound hP
  refine ⟨2000 + Cb + C2, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho c₁ hc₁ hc₁b la hla hgap hsz Z
  have hgood := (GlobalTheory.T.good_weight_antitone_gap hP D T hT j hp hq hE hj Y e o hY la hla fun τ =>
    le_trans (by exact_mod_cast (by omega : 1 ≤ 8 * D.R.f * D.R.r + 10)) (hgap τ)).2 Z
  obtain ⟨s, hsL, hsp, hsn⟩ := h2 D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho c₁ hc₁ hc₁b la hla hgap hsz Z
  haveI : FiniteDimensional Y.d.c₂.F (cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0)) :=
    hgood.1.some.2.1.1.finiteDimensional_of_finite
  obtain ⟨n, w, abelian₂, hsg, hLam, hn⟩ := GlobalTheory.T.exists_short_generators_of_short_spanning_family Y.d.c₂.F _
    (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) s _
    hgood.2.1 (fun σ f => AllWt.petAt_nonneg _ _ _ _ _ _ _)
    (fun σ a f => AllWt.petOn_smul _ _ _ _ Z _ σ a f) (GlobalTheory.T.petersson_norm_component_add_le_of_gramFrame _ _ _ _ Z _ hgood) hsL hsp hsn
  refine ⟨n, w, abelian₂, hsg, ?_⟩

  have hf1 : 1 ≤ D.R.f ∧ 1 ≤ D.R.r := by
    have hn : 1 ≤ D.R.ord := D.R.ord_pos
    have hf : D.R.f = 2 * D.R.ord := rfl
    have hk := D.R.f_le_k
    have ht := D.R.rank_add_five_le
    exact ⟨by omega, by unfold Ranks.r; omega⟩
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1.1
  have hrR : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hf1.2
  set X : ℝ := (D.R.f : ℝ) * D.R.r * Lb with hXdef
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hfR hrR) hLb
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hX2 : X ^ 2 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX3 : X ^ 3 ≤ X ^ 5 := pow_le_pow_right₀ hX (by norm_num)
  have hX23 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX (by norm_num)
  have hX1 : 1 ≤ X ^ 3 := one_le_pow₀ hX
  have hXS : 0 ≤ X ^ 3 * S := mul_nonneg (by positivity) hS
  have hrhs : 0 ≤ (2000 + Cb + C2) * (X ^ 3 * S + X ^ 5) := by positivity
  have hlogd : Real.log (Module.finrank ℚ Y.d.c₂.F : ℝ) ≤ o := hY.deg
  have hdpos : (0 : ℝ) < Module.finrank ℚ Y.d.c₂.F := by exact_mod_cast Module.finrank_pos
  have hdisc : (0 : ℝ) < |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero Y.d.c₂.F)
  have hlrd : Real.log (|((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ))) ≤ o := by
    rw [Real.log_rpow hdisc, one_div, inv_mul_le_iff₀ hdpos, mul_comm]
    exact hY.rd
  have hberg := (hb D T hT j hp hq hE hj Y e o hY Lb hLb hM hfs hfr ho la hla (by linarith) Z).2.2
  have hm : Real.log (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) ≤ Cb * X ^ 3 := hberg
  have ho' : o ≤ 391 * X ^ 2 := ho
  have hCbX : Cb * X ^ 3 ≤ Cb * X ^ 5 := mul_le_mul_of_nonneg_left hX3 hCb
  constructor
  · have hL1 : 1 ≤ abelian₂ := hsg.one_le
    rcases le_or_gt ((Module.finrank ℚ Y.d.c₂.F : ℝ) ^ 4 * (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) *
        |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ)) *
        Real.exp (C2 * (X ^ 3 * S + X ^ 5))) 1 with hB | hB
    · have : abelian₂ = 1 := le_antisymm (hLam.trans (max_le le_rfl hB)) hL1
      rw [this, Real.log_one]; exact hrhs
    · have hLB := hLam.trans (le_of_eq (max_eq_right hB.le))
      have hmpos : (0 : ℝ) < (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        rcases (Nat.cast_nonneg (α := ℝ) (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)))).lt_or_eq with h | h
        · exact h
        · rw [← h] at hB; simp at hB; linarith
      have hrd : 0 < |((NumberField.discr Y.d.c₂.F : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ Y.d.c₂.F : ℝ)) :=
        Real.rpow_pos_of_pos hdisc _
      have hlog := Real.log_le_log (by linarith) hLB
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) hrd.ne',
        Real.log_mul (by positivity) hmpos.ne', Real.log_pow, Real.log_exp] at hlog
      have hC2X : C2 * (X ^ 3 * S + X ^ 5) ≤ C2 * (X ^ 3 * S + X ^ 5) := le_rfl
      nlinarith
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    · have hnR : (n : ℝ) ≤ 2 * (Module.finrank ℚ Y.d.c₂.F : ℝ) * (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        exact_mod_cast hn
      have hmpos : (0 : ℝ) < (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) : ℝ) := by
        have : 0 < Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0)) := by
          rcases Nat.eq_zero_or_pos (Formalism.HN.rkK (latOn Y.U Z (wtOf (T.Q.Dw j) la 0))) with h | h
          · rw [h] at hn; omega
          · exact h
        exact_mod_cast this
      have hlog := Real.log_le_log (by exact_mod_cast hpos) hnR
      rw [Real.log_mul (by positivity) hmpos.ne', Real.log_mul (by norm_num) hdpos.ne'] at hlog
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9; linarith
      have hC2X3 : 0 ≤ C2 * X ^ 3 := by positivity
      nlinarith

end GlobalTheory.ShortGenComp
end
