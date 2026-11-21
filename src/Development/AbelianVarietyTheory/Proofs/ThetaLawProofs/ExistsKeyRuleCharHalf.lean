import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubringsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BasisPowerSectionsLocalBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsCompleteDiscreteValuationRingWithResidues
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAfterDvrExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GenericSectionsMeetTransversally
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZeros
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SignInsert
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SectionsSeparatePointsAndTangents
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfVia
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInvariantAlgClosedTransversal
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomOfIsTranscendenceBasis
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulInvariantLocallyHolomorphicPeriodMatrix
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalAtIffWit
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBPair
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueAtNormalForm
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyRuleCharHalfOfCharZero

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_exists_of_algebraic_invariants : Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic → KaSt → KeyDesc → ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf := by
  first | exact @GlobalTheory.KeyHouse.keyRule_of_kaSt | exact GlobalTheory.KeyHouse.keyRule_of_kaSt | (intros; apply GlobalTheory.KeyHouse.keyRule_of_kaSt <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_quaternion_matrix (m : ℕ) : ∃ A : Matrix (Fin 4) (Fin 4) ℤ,
    A.transpose * A = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  have h' : (m : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]; push_cast; ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_⟩
  rw [h']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.one_apply] <;> ring

theorem exists_admissibleKeyNumericalData_prime_to : ∀ g p : ℕ, 1 ≤ g → p.Prime → ∃ (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted g n l l' al ∧ ¬ p ∣ degProd g n l l' ∧ 1 ≤ degProd g n l l' ∧ 1 ≤ kaExp g n l l' := by
  intro g p hg hp
  choose al hal using exists_quaternion_matrix
  have hp0 := hp.pos
  have hnd : ¬ p ∣ degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) := by
    unfold degProd
    rw [Prime.dvd_finset_prod_iff hp.prime]
    rintro ⟨j, hj, hd⟩
    have hj' : j ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj'
    have e1 : (j + k) * (4 * p) + 1 - j * (4 * p) = p * (4 * k) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    have e2 : (j + k) * (4 * p) + 1 + p - j * (4 * p) = p * (4 * k + 1) + 1 := by
      apply Nat.sub_eq_of_eq_add; ring
    rw [e1, e2] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
    · exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_mul_right _ _)).mp h))
  have hpos : 0 < degProd g (4 * p) (g * (4 * p) + 1) (g * (4 * p) + 1 + p) :=
    Nat.pos_of_ne_zero fun h => hnd (h ▸ dvd_zero p)
  refine ⟨4 * p, g * (4 * p) + 1, g * (4 * p) + 1 + p, al, ⟨by omega, by omega, by omega, hal⟩,
    hnd, hpos, ?_⟩
  unfold kaExp
  have h1 : 0 < g * (4 * p) + 1 + p - (g * (4 * p) + 1) := by omega
  have h2 := Nat.factorial_pos g
  apply Nat.succ_le_of_lt
  positivity

end GlobalTheory.KeyKa
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open TopologicalSpace

namespace GlobalTheory.LineFinite

theorem eq_or_eq_of_dim_le_one {T : Type*} [TopologicalSpace T] [T0Space T] {W : Set T}
    (h : topologicalKrullDim W ≤ 1) {a b c : T} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hab : a ⤳ b) (hbc : b ⤳ c) :
    a = b ∨ b = c := by
  let e : W → IrreducibleCloseds W := fun p => ⟨closure {p}, isIrreducible_singleton.closure, isClosed_closure⟩
  have he : ∀ p q : W, e p ≤ e q ↔ q.1 ⤳ p.1 := fun p q =>
    (specializes_iff_closure_subset (x := q) (y := p)).symm.trans (subtype_specializes_iff q p)
  rcases Order.krullDim_le_one_iff.1 h (e ⟨b, hb⟩) with h' | h'
  · exact Or.inr (hbc.antisymm ((he _ _).1 (h' ((he ⟨c, hc⟩ ⟨b, hb⟩).2 hbc)))).eq
  · exact Or.inl (hab.antisymm ((he _ _).1 (h' ((he ⟨b, hb⟩ ⟨a, ha⟩).2 hab)))).eq

theorem exists_not_isClosed {T : Type*} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] {Z : Set T}
    (hZ : IsClosed Z) (hi : Z.Infinite) : ∃ p ∈ Z, ¬ IsClosed ({p} : Set T) := by
  obtain ⟨S, hS, hc, hirr, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  by_contra hn
  push Not at hn
  refine hi (hS.sUnion fun C hC => ?_)
  obtain ⟨p, hp⟩ := QuasiSober.sober (hirr C hC) (hc C hC)
  have : IsClosed ({p} : Set T) := hn p ⟨C, hC, hp.mem⟩
  rw [← hp.def, this.closure_eq]
  exact Set.finite_singleton p

theorem infinite_closure_inter {T : Type*} [TopologicalSpace T] [JacobsonSpace T] {p : T}
    (hp : ¬ IsClosed ({p} : Set T)) : (closure {p} ∩ closedPoints T).Infinite := by
  intro h
  have hc : IsClosed (closure {p} ∩ closedPoints T) := by
    rw [← Set.biUnion_of_singleton (closure {p} ∩ closedPoints T)]
    exact h.isClosed_biUnion fun x hx => hx.2
  have e := JacobsonSpace.closure_inter_closedPoints (isClosed_closure (s := ({p} : Set T)))
  rw [hc.closure_eq] at e
  exact hp (e.ge (subset_closure rfl)).2

theorem exists_two_fibres {A A' : Type*} [TopologicalSpace A] [TopologicalSpace A'] [NoetherianSpace A']
    [QuasiSober A'] [T0Space A'] [JacobsonSpace A] {φ : A' → A} (hφ : Continuous φ)
    (hirr : ∀ W : Set A, IsClosed W → IsIrreducible W → IsIrreducible (φ ⁻¹' W))
    (hfib : ∀ y : A, IsClosed ({y} : Set A) → (φ ⁻¹' {y}).Subsingleton) {X Z : Set A} (hX : IsClosed X)
    (hZ : Z.Finite) (hd : topologicalKrullDim (φ ⁻¹' X) ≤ 1) {Z' : Set A'} (hZ' : IsClosed Z') (hle : Z' ⊆ φ ⁻¹' X)
    (hi : Z'.Infinite) : ∃ y₁ y₂ : A, y₁ ≠ y₂ ∧ IsClosed ({y₁} : Set A) ∧ IsClosed ({y₂} : Set A) ∧ y₁ ∈ X ∧ y₁ ∉ Z ∧
      φ ⁻¹' {y₁} ⊆ Z' ∧ φ ⁻¹' {y₂} ⊆ Z' := by
  obtain ⟨p, hp, hpc⟩ := exists_not_isClosed hZ' hi
  have hq : ¬ IsClosed ({φ p} : Set A) := fun h => hpc (by
    have := h.preimage hφ
    rwa [(hfib _ h).eq_singleton_of_mem (show p ∈ φ ⁻¹' {φ p} from rfl)] at this)
  have hWX : closure {φ p} ⊆ X := closure_minimal (Set.singleton_subset_iff.2 (hle hp)) hX
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober (hirr _ isClosed_closure (isIrreducible_singleton (x := φ p)).closure)
    (isClosed_closure.preimage hφ)
  obtain ⟨c, hc, hcp⟩ : ∃ c, p ⤳ c ∧ p ≠ c := by
    by_contra hn
    push Not at hn
    refine hpc (closure_subset_iff_isClosed.1 fun c hc => ?_)
    exact (hn c (specializes_iff_mem_closure.2 hc)).symm
  have e : ζ = p := (eq_or_eq_of_dim_le_one hd (hWX hζ.mem) (hle hp) (hle (hc.mem_closed hZ' hp))
    (hζ.specializes (subset_closure (s := {φ p}) rfl)) hc).resolve_right hcp
  subst e
  have hsub : ∀ y ∈ closure {φ ζ}, φ ⁻¹' {y} ⊆ Z' := fun y hy a ha =>
    (hζ.specializes (show φ a ∈ closure {φ ζ} from (show φ a = y from ha) ▸ hy)).mem_closed hZ' hp
  obtain ⟨y₁, h₁, y₂, h₂, hne⟩ := ((infinite_closure_inter hq).sdiff hZ).nontrivial
  exact ⟨y₁, y₂, hne, h₁.1.2, h₂.1.2, hWX h₁.1.1, h₁.2, hsub _ h₁.1.1, hsub _ h₂.1.1⟩

theorem isIrreducible_preimage {k K : Type} [Field k] [IsAlgClosed k] [Field K] {A A' : Scheme.{0}} {φ : A' ⟶ A}
    {p : A ⟶ Sp k} {p' : A' ⟶ Sp K} {f : Sp K ⟶ Sp k} [LocallyOfFiniteType p] (h : IsPullback φ p' p f)
    (W : Set A) (hW : IsClosed W) (hi : IsIrreducible W) : IsIrreducible (φ ⁻¹' W) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := A) ⟨W, hW⟩
  have hI : Set.range I.subschemeι = W := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have : IrreducibleSpace I.subscheme := by
    have := Subtype.irreducibleSpace hi
    have e : I.subscheme ≃ₜ W := (I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hI)
    exact e.irreducibleSpace_iff.2 this
  have hg := GlobalTheory.geometricallyIrreducible_of_isAlgClosed (I.subschemeι ≫ p)
  have : IrreducibleSpace ↥(pullback I.subschemeι φ) := hg.1 f (pullback.fst _ _) (pullback.snd _ _ ≫ p')
    ((IsPullback.of_hasPullback I.subschemeι φ).paste_vert h)
  rw [← hI, ← Scheme.Pullback.range_snd, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ (pullback.snd I.subschemeι φ).continuous.continuousOn

theorem mem_nonzeroLocus_iff {K : Type} [Field K] {X : Scheme.{0}} {M : LB X} (s : LB.Sec M) (w : Sp K ⟶ X) (c : M.ι)
    (h : ⊤ ≤ w ⁻¹ᵁ M.U c) (q : Sp K) : w q ∈ Out.nonzeroLocus s ↔ valT w (M.U c) (s.f c) ≠ 0 := by
  have e₁ : w q ∈ Out.nonzeroLocus s ↔ w q ∈ X.basicOpen (s.f c) := by
    rw [← GlobalTheory.nonzeroLocus_inf_chart s c]
    exact ⟨fun h' => ⟨h', h (show q ∈ ⊤ from trivial)⟩, fun h' => h'.1⟩
  have e₂ := Scheme.basicOpen_appLE w ⊤ (M.U c) h (s.f c)
  rw [basicOpen_eq_of_affine', top_inf_eq] at e₂
  rw [e₁, EtBaseChange.valT_eq _ _ h]
  change q ∈ w ⁻¹ᵁ X.basicOpen (s.f c) ↔ _
  rw [← e₂]
  change EtBaseChange.valH w (M.U c) h (s.f c) ∉ q.asIdeal ↔ _
  rw [show q.asIdeal = ⊥ from congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum K) q ⊥), Ideal.mem_bot]

theorem linearMap_comp_eq_on_smul_of_eq {k K : Type} [Field k] [Field K] [Algebra k K] {N : ℕ} {T : Fin N → K} (hT : LinearIndependent k T)
    (t : K) (a₁ a₂ : k) (β₁ β₂ c : Fin N → k) (ha : a₁ ≠ 0)
    (h₁ : (1 - t) * algebraMap k K a₁ + t * ∑ j, T j * algebraMap k K (β₁ j) = 0)
    (h₂ : (1 - t) * algebraMap k K a₂ + t * ∑ j, T j * algebraMap k K (β₂ j) = 0)
    (hc : ∑ j, c j * β₁ j = 0) : ∑ j, c j * β₂ j = 0 := by
  have ht : t ≠ 0 := by
    rintro rfl
    simp [ha] at h₁
  have h₃ : ∑ j, (a₂ * β₁ j - a₁ * β₂ j) • T j = 0 := by
    have : ∑ j, (a₂ * β₁ j - a₁ * β₂ j) • T j = algebraMap k K a₂ * ∑ j, T j * algebraMap k K (β₁ j) -
        algebraMap k K a₁ * ∑ j, T j * algebraMap k K (β₂ j) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, map_sub, map_mul, map_mul]
      ring
    rw [this]
    refine mul_left_cancel₀ ht ?_
    linear_combination algebraMap k K a₂ * h₁ - algebraMap k K a₁ * h₂
  have h₄ := Fintype.linearIndependent_iff.1 hT _ h₃
  refine mul_left_cancel₀ ha ?_
  have : a₁ * ∑ j, c j * β₂ j = a₂ * ∑ j, c j * β₁ j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    linear_combination (-c j) * h₄ j
  rw [this, hc]
  simp

theorem valT_coords {R : Type} [CommRing R] {x : KeyIn R} {l N : ℕ} {b : Fin N → RR x l} {c : Fin N → R}
    {f : ∀ i, Γ(x.P.A.left, x.P.L.U i)} (hc : Coords x b c f) (z : Pt x) (i : x.P.L.ι)
    (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U i) :
    valT (T := R) z.left (x.P.L.U i) (f i) = ∑ j, c j * valT (T := R) z.left (x.P.L.U i) ((b j).f i) := by
  rw [hc i]
  refine (EtBaseChange.valT_eq (T := R) z.left _ h _).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun j _ => ?_))
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (EtBaseChange.valT_eq (T := R) z.left _ h _).symm)
  exact (EtBaseChange.valT_eq (T := R) z.left _ h _).symm.trans (KoszulCx.valH_cst x z _ h _)

theorem exists_chart_pt {K : Type} [Field K] (x : KeyIn K) (z : Pt x) : ∃ i, ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U i := by
  obtain ⟨i, hi⟩ := exists_chart x.P.isLB (z.left (IsLocalRing.closedPoint K))
  exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map z.left.continuous).mem_open (x.P.L.U i).isOpen hi⟩

section Via
variable {k K : Type} [Field k] [Field K] {x : KeyIn k} {x' : KeyIn K} {f : k →+* K} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}

theorem exists_pt [IsAlgClosed k] (hp : IsPullback φ x'.P.A.hom x.P.A.hom (spMap f)) (y : x.P.A.left)
    (hy : IsClosed ({y} : Set x.P.A.left)) : ∃ (z : Pt x) (z' : Pt x'), (∀ q : Sp k, z.left q = y) ∧
      z'.left ≫ φ = spMap f ≫ z.left ∧ ∀ a, φ a = y → ∃ q : Sp K, z'.left q = a := by
  have := x.P.isAb.proper
  let z : Pt x := Over.homMk (pointOfClosedPoint x.P.A.hom y hy) (pointOfClosedPoint_comp x.P.A.hom y hy)
  have hz : ∀ q : Sp k, z.left q = y := fun q => pointOfClosedPoint_apply x.P.A.hom y hy q
  have hw : (spMap f ≫ z.left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f :=
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w z)).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Pt x' := Over.homMk (hp.lift (spMap f ≫ z.left) (𝟙 _) hw) (hp.lift_snd _ _ _)
  have hz' : z'.left ≫ φ = spMap f ≫ z.left := hp.lift_fst _ _ _
  refine ⟨z, z', hz, hz', fun a ha => ?_⟩
  have sq : IsPullback (spMap f) z'.left z.left φ := by
    refine IsPullback.of_bot (t := hp) ?_ hz'.symm
    have e₁ : z'.left ≫ x'.P.A.hom = 𝟙 _ := Over.w z'
    have e₂ : z.left ≫ x.P.A.hom = 𝟙 _ := Over.w z
    rw [e₁, e₂]
    exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp K)) (f := 𝟙 (Sp k)) (g := spMap f) ⟨by simp⟩
  obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq (IsLocalRing.closedPoint k) a ((hz _).trans ha.symm)
  exact ⟨q, hq⟩

theorem exists_unit (z : Pt x) (z' : Pt x') (hz : z'.left ≫ φ = spMap f ≫ z.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ z'.left ⁻¹ᵁ x'.P.L.U c') (l : ℕ) :
    ∃ u : K, ∀ (s : RR x l) (s' : RR x' l), SecVia x' x φ w s' s →
      f (valT (T := k) z.left (x.P.L.U c) (s.f c)) = u * valT (T := K) z'.left (x'.P.L.U c') (s'.f c') := by
  have hφ : ⊤ ≤ (z'.left ≫ φ) ⁻¹ᵁ x.P.L.U c := fun p _ => by
    rw [hz]
    exact h (show spMap f p ∈ ⊤ from trivial)
  refine ⟨_, fun s s' hs => Eq.trans ?_ (EtBaseChange.valT_via (T := K) hs z'.left c c' hφ h')⟩
  exact ((congrArg (fun q => valT (T := K) q (x.P.L.U c) (s.f c)) hz).trans
    (EtBaseChange.valT_spMap f z.left h _)).symm

theorem relation {n N : ℕ} {b : Fin N → RR x n} {b' : Fin N → RR x' n} (hb : ∀ j, SecVia x' x φ w (b' j) (b j))
    {s : RR x n} {σ s₀ s₁ : RR x' n} (hs : SecVia x' x φ w s₀ s) {T : Fin N → K} (hT : Coords x' b' T s₁.f) {t : K}
    (hσ : ∀ c, (show Γ(x'.P.A.left, x'.P.L.U c) from σ.f c) =
      AbLaw.cst x'.P.A.hom _ (1 - t) * (show Γ(x'.P.A.left, x'.P.L.U c) from s₀.f c) +
        AbLaw.cst x'.P.A.hom _ t * (show Γ(x'.P.A.left, x'.P.L.U c) from s₁.f c))
    (z : Pt x) (z' : Pt x') (hz : z'.left ≫ φ = spMap f ≫ z.left) (c : x.P.L.ι) (h : ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c)
    (q : Sp K) (h0 : z'.left q ∉ Out.nonzeroLocus σ) :
    (1 - t) * f (valT (T := k) z.left (x.P.L.U c) (s.f c)) +
      t * ∑ j, T j * f (valT (T := k) z.left (x.P.L.U c) ((b j).f c)) = 0 := by
  obtain ⟨c', h'⟩ := exists_chart_pt x' z'
  obtain ⟨u, hu⟩ := exists_unit (w := w) z z' hz c c' h h' n
  have e₀ : valT (T := K) z'.left (x'.P.L.U c') (σ.f c') = 0 :=
    not_not.1 fun e => h0 ((mem_nonzeroLocus_iff σ z'.left c' h' q).2 e)
  have e₁ : valT (T := K) z'.left (x'.P.L.U c') (σ.f c') =
      (1 - t) * valT (T := K) z'.left (x'.P.L.U c') (s₀.f c') + t * valT (T := K) z'.left (x'.P.L.U c') (s₁.f c') := by
    have v := EtBaseChange.valT_eq (T := K) z'.left _ h'
    refine (congrArg (valT (T := K) z'.left (x'.P.L.U c')) (hσ c')).trans ((v _).trans ((map_add _ _ _).trans ?_))
    refine congrArg₂ (· + ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (v _).symm))
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (v _).symm))
    · exact (v _).symm.trans (KoszulCx.valH_cst x' z' _ h' _)
    · exact (v _).symm.trans (KoszulCx.valH_cst x' z' _ h' _)
  have e₂ := valT_coords hT z' c' h'
  have e₃ : ∑ j, T j * f (valT (T := k) z.left (x.P.L.U c) ((b j).f c)) =
      u * valT (T := K) z'.left (x'.P.L.U c') (s₁.f c') := by
    rw [e₂, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (congrArg (T j * ·) (hu _ _ (hb j))).trans (mul_left_comm _ _ _)
  rw [e₃, hu _ _ hs]
  linear_combination u * (e₁.symm.trans e₀)

end Via

end GlobalTheory.LineFinite

open GlobalTheory.LineFinite in

theorem GlobalTheory.KeyKa.finZ_of_line_towards_generic : Out.Laws → ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n : ℕ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (r : ℕ) (s : Fin r → RR x n) (s' : Fin r → RR x' n) (i₀ : Fin r) (s₀ s₁ : RR x' n) (T : Fin (n ^ x.P.g) → K) (t : K), 4 ≤ n → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → FinZ x s → AlgebraicIndependent k T → (∀ i, i ≠ i₀ → SecVia x' x φ w (s' i) (s i)) → SecVia x' x φ w s₀ (s i₀) → Coords x' b' T s₁.f → (∀ c, (show Γ(x'.P.A.left, x'.P.L.U c) from (s' i₀).f c) = AbLaw.cst x'.P.A.hom _ (1 - t) * (show Γ(x'.P.A.left, x'.P.L.U c) from s₀.f c) + AbLaw.cst x'.P.A.hom _ t * (show Γ(x'.P.A.left, x'.P.L.U c) from s₁.f c)) → FinZ x' s' := by
  intro hL k K _ _ _ _ _ x x' φ w n b b' r s s' i₀ s₀ s₁ T t hn ⟨_, _, _, hp, _⟩ hb hb' hs hT hs' hs₀ hs₁ hσ
  have := x.P.isAb.proper
  have := x'.P.isAb.proper
  have := LocallyOfFiniteType.jacobsonSpace x.P.A.hom
  have := LocallyOfFiniteType.isLocallyNoetherian x'.P.A.hom
  have : CompactSpace x'.P.A.left := QuasiCompact.compactSpace_of_compactSpace x'.P.A.hom
  have : IsNoetherian x'.P.A.left := {}
  have cl : ∀ {Y : Scheme.{0}} {J : Type} (P : J → Prop) (D : J → Y.Opens), IsClosed {y : Y | ∀ i, P i → y ∉ D i} :=
    fun P D => by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => (D i).isOpen.isClosed_compl
  have hfib : ∀ y : x.P.A.left, IsClosed ({y} : Set x.P.A.left) → (φ ⁻¹' {y}).Subsingleton := fun y hy a ha a' ha' => by
    obtain ⟨z, z', -, -, h⟩ := exists_pt hp.1 y hy
    obtain ⟨q, rfl⟩ := h a ha
    obtain ⟨q', rfl⟩ := h a' ha'
    exact congrArg z'.left (Subsingleton.elim (α := PrimeSpectrum K) q q')
  let X : Set x.P.A.left := {y | ∀ i, i ≠ i₀ → y ∉ Out.nonzeroLocus (s i)}
  let Z : Set x.P.A.left := {y | ∀ i, y ∉ Out.nonzeroLocus (s i)}
  let Z' : Set x'.P.A.left := {y | ∀ i, y ∉ Out.nonzeroLocus (s' i)}
  have hX : IsClosed X := cl _ _
  have hZ : IsClosed Z := by simpa using cl (fun _ => True) fun i => Out.nonzeroLocus (s i)
  have hZ' : IsClosed Z' := by simpa using cl (fun _ => True) fun i => Out.nonzeroLocus (s' i)
  have hle : Z' ⊆ φ ⁻¹' X := fun y hy i hi h => hy i (EtBaseChange.mem_nonzeroLocus_via (hs' i hi) y h)
  by_contra hi
  have hi' : Z'.Infinite := hi
  have hfin : (φ ⁻¹' Z).Finite := Set.Finite.preimage' hs fun y hy =>
    (hfib y (GlobalTheory.DimCut.isClosed_singleton_of_finite hZ hs hy)).finite
  have hd : topologicalKrullDim (φ ⁻¹' X) ≤ 1 := by
    have := GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros hL K x' n 1 (fun _ => s₀) (φ ⁻¹' X) (by omega)
      (hX.preimage φ.continuous) (hi'.nonempty.mono hle) (hfin.subset fun y hy i h => by
        by_cases e : i = i₀
        · subst e
          exact hy.2 0 (EtBaseChange.mem_nonzeroLocus_via hs₀ y h)
        · exact hy.1 i e h)
    exact_mod_cast this
  obtain ⟨y₁, y₂, hne, c₁, c₂, hX₁, hZ₁, l₁, l₂⟩ := exists_two_fibres φ.continuous (isIrreducible_preimage hp.1) hfib
    hX (Z := Z) hs hd hZ' hle hi'
  obtain ⟨z₁, z₁', p₁, e₁, -⟩ := exists_pt hp.1 y₁ c₁
  obtain ⟨z₂, z₂', p₂, e₂, -⟩ := exists_pt hp.1 y₂ c₂
  obtain ⟨d₁, h₁⟩ := exists_chart_pt x z₁
  obtain ⟨d₂, h₂⟩ := exists_chart_pt x z₂
  let q : Sp K := IsLocalRing.closedPoint K
  let q₀ : Sp k := IsLocalRing.closedPoint k
  have r₁ := relation hb' hs₀ hs₁ hσ z₁ z₁' e₁ d₁ h₁ q
    (l₁ (show φ (z₁'.left q) = y₁ from (congrArg (fun m => m q) e₁).trans (p₁ _)) i₀)
  have r₂ := relation hb' hs₀ hs₁ hσ z₂ z₂' e₂ d₂ h₂ q
    (l₂ (show φ (z₂'.left q) = y₂ from (congrArg (fun m => m q) e₂).trans (p₂ _)) i₀)
  have ha : valT (T := k) z₁.left (x.P.L.U d₁) ((s i₀).f d₁) ≠ 0 := by
    refine (mem_nonzeroLocus_iff (s i₀) z₁.left d₁ h₁ q₀).1 ?_
    by_contra h
    refine hZ₁ fun i => ?_
    by_cases e : i = i₀
    · rw [e, ← p₁ q₀]
      exact h
    · exact hX₁ i e
  obtain ⟨σ, hσ₁, hσ₂⟩ := (GlobalTheory.KeyKa.sections_separate_points_and_tangents hL k x n hn).2 z₁ z₂ d₁ d₂
    (fun e => hne ((p₁ q₀).symm.trans (e ▸ p₂ q₀))) h₁ h₂
  obtain ⟨c, hc, -⟩ := hb σ
  exact hσ₂ ((valT_coords hc z₂ d₂ h₂).trans (linearMap_comp_eq_on_smul_of_eq hT.linearIndependent t _ _ _ _ c ha r₁ r₂
    ((valT_coords hc z₁ d₁ h₁).symm.trans hσ₁)))
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyGeneric

section Sec

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem gs_pow' {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs r z U (a ^ n) = gs r z U a ^ n := by simp only [gs_eq r z U h, map_pow]

theorem via_iff_stalk (w : LB.Iso L' (L.pull F)) (l : ℕ) (a' : ∀ i, Γ(X', L'.U i)) (a : ∀ j, Γ(X, L.U j)) :
    GlobalTheory.KeyVia.Via w l a' a ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (a j) = (gw w r z j k).val ^ l * gs r z _ (a' k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ L.U j := fun y hy => mem_pull.1 hy.1
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy, gs_pow' _ z _ hy]
    exact congrArg (· ^ l * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy, gs_pow' _ y _ hy]
    exact congrArg (· ^ l * _) (gs_unit _ y _ hy _).symm

end Sec

theorem keyVia_cancel {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {x : KeyIn R} {x' : KeyIn R'}
    {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''} {φ w φ'' w''} (h : KeyVia x' x f φ w)
    (h'' : KeyVia x'' x (f'.comp f) φ'' w'') :
    ∃ φ' w', KeyVia x'' x' f' φ' w' ∧ ∀ (l : ℕ) (s : RR x l) (s' : RR x' l) (s'' : RR x'' l),
      SecVia x' x φ w s' s → SecVia x'' x φ'' w'' s'' s → SecVia x'' x' φ' w' s'' s' := by
  obtain ⟨he, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := h
  obtain ⟨he'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := h''
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x''.P.A.left ⟶ x'.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x'.P.A.hom = x''.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x''.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x''.P.A ≫ φ' = spMap f' ≫ eSec x'.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x''.P.A ≫ x''.P.A.hom = 𝟙 _ := Over.w η[x''.P.A]
      have a₂ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel x.P.isLB w w'' g g'' x'.P.isLB x''.P.isLB
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ (spMap f) he x.P.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec x.P.A) _ x''.rig x.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' x.P.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp F = F'' := GlobalTheory.KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', w', ⟨he', hg''.trans hg.symm, Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel x.P.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _ (rigPull_le φ' (spMap f') he' x'.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel x.P.isLB (fun _ => he') r r''),
    (GlobalTheory.KeyCancel.appLE_eq_iff_stalk w' x'.th x''.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩,
    fun l s s' s'' hs' hs'' => (via_iff_stalk w' l s''.f s'.f).2 fun Z q z i k hi hk => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (GlobalTheory.KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (GlobalTheory.KeyCancel.appLE_eq_iff_stalk w'' x.th x''.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, ← hFF, ← Category.assoc]
      congr 1
      show Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · obtain ⟨j, hj⟩ := exists_chart x.P.isLB (φ (φ' (q z)))
    have a := (via_iff_stalk w l s'.f s.f).1 hs' Z (q ≫ φ') z j i hj hi
    have b := (via_iff_stalk w'' l s''.f s.f).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, mul_pow, _root_.mul_assoc] at b
    exact ((Units.isUnit _).pow l).mul_left_cancel b

theorem exists_coords {R : Type} [CommRing R] (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) :
    ∃ s : RR x l, Coords x b c s.f := by
  refine ⟨⟨fun i => ∑ k, GlobalTheory.AbLaw.cst x.P.A.hom (x.P.L.U i) (c k) * (show Γ(x.P.A.left, x.P.L.U i) from (b k).f i),
    fun i j => ?_⟩, fun i => rfl⟩
  refine (map_sum _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (map_sum _ _ _).symm))
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (Finset.mul_sum _ _ _).symm
  refine (map_mul _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (map_mul _ _ _).symm))
  refine (congrArg₂ (· * ·) ((rs_cst _ _ _).trans (rs_cst _ _ _).symm) ((b k).compat i j)).trans (mul_left_comm _ _ _)

theorem finZ_of_etZ {K : Type} [Field K] {x : KeyIn K} {n d : ℕ} {s : Fin x.P.g → RR x n} {z : Fin d → Pt x}
    {ch : Fin d → x.P.L.ι} (h : EtZ x s z ch) : FinZ x s := by
  haveI : Finite (Sp K) := inferInstanceAs (Finite (PrimeSpectrum K))
  refine (Set.finite_range fun q : Fin d × Sp K => (z q.1).left q.2).subset fun y hy => ?_
  obtain ⟨a, p, e⟩ := h.2.2.2.2 y hy
  exact ⟨(a, p), e⟩

theorem degProd_ne_zero {g n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (h : admitted g n l l' al) :
    degProd g n l l' ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
  have hj' : j * n ≤ g * n := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  obtain ⟨-, h₁, h₂, -⟩ := h
  exact mul_ne_zero (by omega) (by omega)

theorem exists_field {k K I I' : Type} [Field k] [Field K] [IsAlgClosed K] [Algebra k K] {U : I → K} {V : I' → K}
    (h : AlgebraicIndependent k (Sum.elim V U)) :
    ∃ (E : IntermediateField k K) (U' : I → E), IsAlgClosed E ∧ (∀ i, (U' i : K) = U i) ∧
      AlgebraicIndependent k U' ∧ AlgebraicIndependent E V := by
  obtain ⟨h₁, h₂⟩ := AlgebraicIndependent.sumElim_iff.1 h
  have h₃ := IntermediateField.algebraicIndependent_adjoin_iff.2 h₂
  let A := IntermediateField.adjoin k (Set.range U)
  have h₄ : AlgebraicIndependent (algebraicClosure A K) V := h₃.algebraicClosure
  refine ⟨(algebraicClosure A K).restrictScalars k, fun i => ⟨U i, ?_⟩, (algebraicClosure.isAlgClosure A K).isAlgClosed,
    fun _ => rfl, ?_, h₄⟩
  · exact (algebraicClosure A K).algebraMap_mem ⟨U i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩
  · exact AlgebraicIndependent.of_comp (IntermediateField.val _) h₁

theorem secVia_of_coords {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {φ w}
    (h : KeyVia x' x f φ w) {l N : ℕ} {b : Fin N → RR x l} {b' : Fin N → RR x' l} (hb : ∀ j, SecVia x' x φ w (b' j) (b j))
    {c : Fin N → R} {s : RR x l} {s' : RR x' l} (hs : Coords x b c s.f) (hs' : Coords x' b' (fun j => f (c j)) s'.f) :
    SecVia x' x φ w s' s := by
  obtain ⟨σ, hσ, -⟩ := ((GlobalTheory.KeyVia.main R R' x x' f).2 φ w h).1 l s
  have e := ((GlobalTheory.KeyVia.main R R' x x' f).2 φ w h).2.2 l N b b' s σ c hb hσ hs
  have e' : σ.f = s'.f := funext fun i => (e i).trans (hs' i).symm
  obtain ⟨tf, _⟩ := σ
  obtain ⟨sf, _⟩ := s'
  obtain rfl : tf = sf := e'
  exact hσ

theorem finZ_of_generic (hL : Out.Laws) {k K : Type} [Field k] [Field K] [IsAlgClosed K] [Algebra k K] {x : KeyIn k}
    {x' : KeyIn K} {φ w} {n G : ℕ} (hG : x'.P.g = G) {b : Fin (n ^ x.P.g) → RR x n} {b' : Fin (n ^ x.P.g) → RR x' n}
    {T : Fin G × Fin (n ^ x.P.g) → K} {s : Fin G → RR x' n} (hn : 4 ≤ n) (h : KeyVia x' x (algebraMap k K) φ w)
    (hb : IsBasis x b) (hb' : ∀ j, SecVia x' x φ w (b' j) (b j)) (hT : AlgebraicIndependent k T)
    (hs : ∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) : FinZ x' s := by
  subst hG
  obtain ⟨d, z, ch, H⟩ := GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent hL k K x x' φ w n b b' T s hn h hb hb' hT hs
  exact finZ_of_etZ H

theorem finZ_line (hL : Out.Laws) {k K : Type} [Field k] [Field K] [IsAlgClosed K] [Algebra k K] {x : KeyIn k}
    {x' : KeyIn K} {φ w} {n : ℕ} {b : Fin (n ^ x.P.g) → RR x n} {b' : Fin (n ^ x.P.g) → RR x' n}
    {U : Fin x'.P.g × Fin (n ^ x.P.g) → K} {V : Fin (n ^ x.P.g) → K} {s σ : Fin x'.P.g → RR x' n} {s₁ : RR x' n}
    (hn : 4 ≤ n) (h : KeyVia x' x (algebraMap k K) φ w) (hb : IsBasis x b) (hb' : ∀ j, SecVia x' x φ w (b' j) (b j))
    (hT : AlgebraicIndependent k (Sum.elim V U)) (hs : ∀ i, Coords x' b' (fun j => U (i, j)) (s i).f)
    (hs₁ : Coords x' b' V s₁.f) (i₀ : Fin x'.P.g) (t : K) (hσ : ∀ i, i ≠ i₀ → (σ i).f = (s i).f)
    (hσ₀ : ∀ c, (show Γ(x'.P.A.left, x'.P.L.U c) from (σ i₀).f c) =
      GlobalTheory.AbLaw.cst x'.P.A.hom _ (1 - t) * (show Γ(x'.P.A.left, x'.P.L.U c) from (s i₀).f c) +
        GlobalTheory.AbLaw.cst x'.P.A.hom _ t * (show Γ(x'.P.A.left, x'.P.L.U c) from s₁.f c)) : FinZ x' σ := by
  obtain ⟨E, U', hE, hU', hUi, hVi⟩ := exists_field hT
  obtain ⟨y, hy⟩ := GlobalTheory.KeyPow.keyIn_baseChange hL.polBaseChange k E x (algebraMap k E)
  obtain ⟨φ₁, w₁, h₁⟩ := (GlobalTheory.KeyVia.main k E x y _).1.1 hy
  have h' : KeyVia x' x ((algebraMap E K).comp (algebraMap k E)) φ w := by
    rw [← IsScalarTower.algebraMap_eq]; exact h
  obtain ⟨φ₂, w₂, h₂, hc⟩ := keyVia_cancel h₁ h'
  choose b₁ hb₁ using fun j => (((GlobalTheory.KeyVia.main k E x y _).2 φ₁ w₁ h₁).1 n (b j)).exists
  have hb₂ : ∀ j, SecVia x' y φ₂ w₂ (b' j) (b₁ j) := fun j => hc n _ _ _ (hb₁ j) (hb' j)
  have hB : IsBasis y b₁ := (GlobalTheory.KeyBasis.main hL k x n (by omega)).2 b hb E _ y φ₁ w₁ b₁ h₁ hb₁
  choose r hr using fun i : Fin x'.P.g => exists_coords y b₁ fun j => U' (i, j)
  have hg₁ : y.P.g = x.P.g := h₁.2.1
  have hg₂ : x'.P.g = y.P.g := h₂.2.1
  have hfin : FinZ y r := finZ_of_generic hL hg₂.symm hn h₁ hb hb₁ hUi hr
  have hrs : ∀ i, SecVia x' y φ₂ w₂ (s i) (r i) := fun i => secVia_of_coords h₂ hb₂ (hr i) <| by
    have e : (fun j => algebraMap E K (U' (i, j))) = fun j => U (i, j) := funext fun j => hU' _
    rw [e]; exact hs i
  have key : ∀ (N : ℕ) (_ : n ^ y.P.g = N) (b₁ : Fin N → RR y n) (b' : Fin N → RR x' n) (V : Fin N → K),
      IsBasis y b₁ → (∀ j, SecVia x' y φ₂ w₂ (b' j) (b₁ j)) → AlgebraicIndependent E V → Coords x' b' V s₁.f →
      FinZ x' σ := by
    rintro N rfl b₁ b' V hB hb₂ hVi hs₁
    refine GlobalTheory.KeyKa.finZ_of_line_towards_generic hL E K y x' φ₂ w₂ n b₁ b' _ r σ i₀ (s i₀) s₁ V t hn h₂ hB hb₂ hfin hVi (fun i hi => ?_) (hrs i₀)
      hs₁ hσ₀
    have e := hσ i hi
    intro j a hh
    rw [e]
    exact hrs i j a hh
  exact key _ (by rw [hg₁]) b₁ b' V hB hb₂ hVi hs₁

theorem kaVal_eq_of_generic : Out.Laws → ∀ (k K : Type) [Field k] [CharZero k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T T' : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s s' : Fin x'.P.g → RR x' n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k (Sum.elim T T') → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → (∀ i, Coords x' b' (fun j => T' (i, j)) (s' i).f) → KaVal x' n l l' al s κ → KaVal x' n l l' al s' κ' → κ = κ' := by
  intro hL k K _ _ _ _ _ x x' φ w n l l' al b b' T T' s s' κ κ' hA h hb hb' hT hs hs' hκ hκ'
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have hg : x'.P.g = x.P.g := h.2.1
  have hA' : admitted x'.P.g n l l' al := by rw [hg]; exact hA
  have hn : 4 ≤ n := hA.1
  let sl : Finset (Fin x'.P.g) → Fin x'.P.g × Fin (n ^ x.P.g) →
      (Fin x'.P.g × Fin (n ^ x.P.g)) ⊕ (Fin x'.P.g × Fin (n ^ x.P.g)) :=
    fun S p => if p.1 ∈ S then Sum.inr p else Sum.inl p
  have hsl : ∀ S p, Sum.elim id id (sl S p) = p := fun S p => by
    by_cases hp : p.1 ∈ S <;> simp [sl, hp]
  have hco : ∀ S i, Coords x' b' (fun j => Sum.elim T T' (sl S (i, j))) (S.piecewise s' s i).f := fun S i => by
    by_cases hp : i ∈ S
    · simpa [sl, hp] using hs' i
    · simpa [sl, hp] using hs i
  have main : ∀ (S : Finset (Fin x'.P.g)) (ρ : Kˣ), KaVal x' n l l' al (S.piecewise s' s) ρ → κ = ρ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro ρ hρ
      rw [Finset.piecewise_empty] at hρ
      refine GlobalTheory.KeyLine.kaVal_eq_of_line hL K x' n l l' al s s κ ρ hA' (fun t σ hσ => ?_) hκ hρ
      refine finZ_of_generic hL rfl hn h hb hb' (T := T) (hT.comp Sum.inl Sum.inl_injective) fun i c => ?_
      refine (hσ i c).trans (Eq.trans ?_ (hs i c))
      rw [← add_mul, ← map_add, sub_add_cancel, map_one, _root_.one_mul]
    | insert i₀ S hi ih =>
      intro ρ hρ
      have hinj : Function.Injective (sl S) := Function.LeftInverse.injective (hsl S)
      obtain ⟨d, z, ch, H⟩ := GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent hL k K x x' φ w n b b' (Sum.elim T T' ∘ sl S) _ hn h hb hb'
        (hT.comp _ hinj) (hco S)
      obtain ⟨ν, hν⟩ := GlobalTheory.KeyKa.exists_kaVal_of_isAlgClosed hL K x' n l l' al d _ z ch hA' (Nat.cast_ne_zero.2 (degProd_ne_zero hA')) H
      refine (ih ν hν).trans (GlobalTheory.KeyLine.kaVal_eq_of_line hL K x' n l l' al _ _ ν ρ hA' (fun t σ hσ => ?_) hν hρ)
      have hinj' : Function.Injective (Sum.elim (fun j => Sum.inr (i₀, j)) (sl S)) := by
        refine Function.Injective.sumElim (fun j j' e => by simpa using e) hinj fun j p e => ?_
        have e' : (i₀, j) = p := (congrArg (Sum.elim id id) e).trans (hsl S p)
        subst e'
        simp [sl, hi] at e
      have hT' : AlgebraicIndependent k (Sum.elim (fun j => T' (i₀, j)) (Sum.elim T T' ∘ sl S)) := by
        have := hT.comp _ hinj'
        rwa [Sum.comp_elim] at this
      refine finZ_line hL hn h hb hb' hT' (hco S) (hs' i₀) i₀ t (fun i hi' => funext fun c => (hσ i c).trans ?_)
        fun c => ?_
      · rw [Finset.piecewise_insert_of_ne _ _ _ hi', ← add_mul, ← map_add, sub_add_cancel, map_one, _root_.one_mul]
      · have := hσ i₀ c
        rwa [Finset.piecewise_insert_self] at this
  exact main Finset.univ κ' (by rwa [Finset.piecewise_univ])

end GlobalTheory.KeyGeneric
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyInvariant_eq_of_independent_generic_tuples : Out.Laws → ∀ (k K : Type) [Field k] [CharZero k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T T' : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s s' : Fin x'.P.g → RR x' n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k (Sum.elim T T') → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → (∀ i, Coords x' b' (fun j => T' (i, j)) (s' i).f) → KaVal x' n l l' al s κ → KaVal x' n l l' al s' κ' → κ = κ' := by
  atlas_forward_decl GlobalTheory.KeyGeneric.kaVal_eq_of_generic
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyInvariant_algClosed_transversal : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (d : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), admitted x.P.g n l l' al → ((degProd x.P.g n l l' : ℕ) : K) ≠ 0 → EtZ x s z ch → ∃ κ, KaVal x n l l' al s κ := by
  first | exact @GlobalTheory.KeyKa.exists_kaVal_of_isAlgClosed | exact GlobalTheory.KeyKa.exists_kaVal_of_isAlgClosed | (intros; apply GlobalTheory.KeyKa.exists_kaVal_of_isAlgClosed <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_sections_meet_transversally : Out.Laws → ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] [Algebra k K] (x : KeyIn k) (x' : KeyIn K) φ w (n : ℕ) (b : Fin (n ^ x.P.g) → RR x n) (b' : Fin (n ^ x.P.g) → RR x' n) (T : Fin x'.P.g × Fin (n ^ x.P.g) → K) (s : Fin x'.P.g → RR x' n), 4 ≤ n → KeyVia x' x (algebraMap k K) φ w → IsBasis x b → (∀ j, SecVia x' x φ w (b' j) (b j)) → AlgebraicIndependent k T → (∀ i, Coords x' b' (fun j => T (i, j)) (s i).f) → ∃ (d : ℕ) (z : Fin d → Pt x') (ch : Fin d → x'.P.L.ι), EtZ x' s z ch := by
  first | exact @GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent | exact GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent | (intros; apply GlobalTheory.KeyKa.GenericZeros.exists_etZ_of_algebraicIndependent <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KaIndep

theorem exists_coords {R : Type} [CommRing R] (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) :
    ∃ s : RR x l, Coords x b c s.f := by
  refine ⟨⟨fun i => ∑ k, cst x.P.A.hom ((pw x.P.L (l : ℤ)).U i) (c k) * (b k).f i, ?_⟩, fun i => rfl⟩
  intro i j
  have e4 : ∀ (V W : x.P.A.left.Opens) (h : W ≤ V) (a : R),
      (x.P.A.left.presheaf.map (homOfLE h).op).hom (cst x.P.A.hom V a) = cst x.P.A.hom W a := by
    intro V W h a
    simp only [AbLaw.cst, RingHom.comp_apply]
    exact GlobalTheory.KeyVia.res_appLE (φ := x.P.A.hom) (U := ⊤) _ h _
  simp only [map_sum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e3 := (b k).compat i j
  rw [e4, e4, e3]
  ring

theorem eq_of_coords {R : Type} [CommRing R] {x : KeyIn R} {l N : ℕ} {b : Fin N → RR x l} {c : Fin N → R}
    {s t : RR x l} (hs : Coords x b c s.f) (ht : Coords x b c t.f) : s = t := by
  have hf : s.f = t.f := funext fun i => (hs i).trans (ht i).symm
  cases s
  cases t
  cases hf
  rfl

theorem degProd_ne_zero {g n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (h : admitted g n l l' al) :
    degProd g n l l' ≠ 0 := by
  obtain ⟨-, hl, hl', -⟩ := h
  unfold degProd
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have hj' : j ≤ g := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hjn : j * n ≤ g * n := Nat.mul_le_mul_right n hj'
  apply mul_ne_zero <;> omega

variable {K : Type} [Field K] {x : KeyIn K} {n : ℕ}

def Framed (b : Fin (n ^ x.P.g) → RR x n) {R : Type} [CommRing R] (f : K →+* R)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (x' : KeyIn R) (s : Fin x'.P.g → RR x' n) : Prop :=
  ∃ φ w, ∃ (hg : x'.P.g = x.P.g) (b' : Fin (n ^ x.P.g) → RR x' n), KeyVia x' x f φ w ∧
    (∀ k, SecVia x' x φ w (b' k) (b k)) ∧ ∀ i, Coords x' b' (fun k => T (i.cast hg, k)) (s i).f

variable {b : Fin (n ^ x.P.g) → RR x n}

theorem exists_framed (b : Fin (n ^ x.P.g) → RR x n) {R : Type} [CommRing R] (f : K →+* R)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) : ∃ x' s, Framed b f T x' s := by
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x f
  obtain ⟨φ, w, H⟩ := (GlobalTheory.KeyVia.main K R x x' f).1.1 hx'
  obtain ⟨_, hg, _⟩ := id H
  have M := (GlobalTheory.KeyVia.main K R x x' f).2 φ w H
  choose b' hb' _ using fun k => M.1 n (b k)
  choose s hs using fun i : Fin x'.P.g => exists_coords x' b' (fun k => T (i.cast hg, k))
  exact ⟨x', s, φ, w, hg, b', H, hb', hs⟩

theorem Framed.g_eq {R : Type} [CommRing R] {f : K →+* R} {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R}
    {s : Fin x'.P.g → RR x' n} (h : Framed b f T x' s) : x'.P.g = x.P.g := by
  obtain ⟨_, _, hg, _⟩ := h
  exact hg

theorem Framed.via {R R' : Type} [CommRing R] [CommRing R'] {f : K →+* R} {j : R →+* R'}
    {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R} {s : Fin x'.P.g → RR x' n} {x'' : KeyIn R'}
    {s' : Fin x''.P.g → RR x'' n} (h : Framed b f T x' s) (h' : Framed b (j.comp f) (j ∘ T) x'' s') :
    ∃ φ w, ∃ hg : x''.P.g = x'.P.g, KeyVia x'' x' j φ w ∧ ∀ i, SecVia x'' x' φ w (s' i) (s (i.cast hg)) := by
  obtain ⟨φ1, w1, hg1, b1, H1, hb1, hs1⟩ := h
  obtain ⟨φ2, w2, hg2, b2, H2, hb2, hs2⟩ := h'
  obtain ⟨φ, w, H, -, hsec⟩ := GlobalTheory.KaLift.keyVia_cancel H1 H2
  have hg : x''.P.g = x'.P.g := hg2.trans hg1.symm
  refine ⟨φ, w, hg, H, fun i => ?_⟩
  have hb : ∀ k, SecVia x'' x' φ w (b2 k) (b1 k) := fun k => hsec n (b k) (b1 k) (b2 k) (hb1 k) (hb2 k)
  have M := (GlobalTheory.KeyVia.main R R' x' x'' j).2 φ w H
  obtain ⟨t, ht, -⟩ := M.1 n (s (i.cast hg))
  have hc := M.2.2 n (n ^ x.P.g) b1 b2 (s (i.cast hg)) t (fun k => T ((i.cast hg).cast hg1, k)) hb ht (hs1 _)
  have e : (i.cast hg).cast hg1 = i.cast hg2 := Fin.ext rfl
  rw [e] at hc
  have ht' : t = s' i := eq_of_coords hc (hs2 i)
  rw [← ht']
  exact ht

variable {l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ}

theorem Framed.kaVal (hL : Out.Laws) (hA : admitted x.P.g n l l' al) {R R' : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] {f : K →+* R} {j : R →+* R'}
    {T : Fin x.P.g × Fin (n ^ x.P.g) → R} {x' : KeyIn R} {s : Fin x'.P.g → RR x' n} {x'' : KeyIn R'}
    {s' : Fin x''.P.g → RR x'' n} (h : Framed b f T x' s) (h' : Framed b (j.comp f) (j ∘ T) x'' s') {κ : Rˣ}
    (hκ : KaVal x' n l l' al s κ) : KaVal x'' n l l' al s' (Units.map j.toMonoidHom κ) := by
  obtain ⟨φ, w, hg, H, hs⟩ := h.via h'
  have hA' : admitted x'.P.g n l l' al := by rw [h.g_eq]; exact hA
  exact GlobalTheory.T.keyInvariant_baseChange hL R R' x' x'' j φ w n l l' al hg s s' κ hA' H hs hκ

def ValAt (b : Fin (n ^ x.P.g) → RR x n) (l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (R : Type) [CommRing R]
    [Algebra K R] (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) : Prop :=
  ∃ x' s, ∃ κ : Rˣ, Framed b (algebraMap K R) T x' s ∧ KaVal x' n l l' al s κ ∧ a = κ

theorem valAt_map (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (R R' : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] [Algebra K R] [Algebra K R'] (j : R →ₐ[K] R')
    (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) (h : ValAt b l l' al R T a) : ValAt b l l' al R' (j ∘ T) (j a) := by
  obtain ⟨x', s, κ, hf, hκ, rfl⟩ := h
  obtain ⟨x'', s'', hf''⟩ := exists_framed b (algebraMap K R') (j ∘ T)
  have e : (j : R →+* R').comp (algebraMap K R) = algebraMap K R' := j.comp_algebraMap
  have hf2 : Framed b ((j : R →+* R').comp (algebraMap K R)) ((j : R →+* R') ∘ T) x'' s'' := by
    rw [e]; exact hf''
  exact ⟨x'', s'', _, hf'', hf.kaVal hL hA hf2 hκ, rfl⟩

theorem valAt_unique [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (F : Type) [Field F] [Algebra K F]
    (T : Fin x.P.g × Fin (n ^ x.P.g) → F) (a a' : F) (h : ValAt b l l' al F T a) (h' : ValAt b l l' al F T a') :
    a = a' := by
  obtain ⟨x1, s1, κ1, h1, hk1, rfl⟩ := h
  obtain ⟨x2, s2, κ2, h2, hk2, rfl⟩ := h'
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have h2' : Framed b ((RingHom.id F).comp (algebraMap K F)) (RingHom.id F ∘ T) x2 s2 := by
    simpa only [RingHom.id_comp, RingHom.coe_id, Function.id_comp] using h2
  have hk := h1.kaVal hL hA h2' hk1
  have hA2 : admitted x2.P.g n l l' al := by rw [h2.g_eq]; exact hA
  have e := GlobalTheory.T.keyInvariantFromIntersection_unique hL F x2 n l l' al s2 _ _ hA2 hk hk2
  rw [← e]
  rfl

theorem exists_valAt [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (hb : IsBasis x b) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (T : Fin x.P.g × Fin (n ^ x.P.g) → Ω) (hT : AlgebraicIndependent K T) :
    ∃ a, ValAt b l l' al Ω T a := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨x', s, hf⟩ := exists_framed b (algebraMap K Ω) T
  obtain ⟨φ, w, hg, b', H, hb', hs⟩ := id hf
  have hA' : admitted x'.P.g n l l' al := by rw [hg]; exact hA
  have hinj : Function.Injective
      (fun p : Fin x'.P.g × Fin (n ^ x.P.g) => ((p.1.cast hg, p.2) : Fin x.P.g × Fin (n ^ x.P.g))) :=
    fun p q hpq => Prod.ext (Fin.ext (congrArg (fun r => (r.1 : ℕ)) hpq)) (congrArg (fun r => r.2) hpq)
  obtain ⟨d, z, ch, hz⟩ := GlobalTheory.T.generic_sections_meet_transversally hL K Ω x x' φ w n b b' (fun p => T (p.1.cast hg, p.2)) s hA.1 H hb hb'
    (hT.comp _ hinj) hs
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_keyInvariant_algClosed_transversal hL Ω x' n l l' al d s z ch hA'
    (Nat.cast_ne_zero.mpr (degProd_ne_zero hA')) hz
  exact ⟨κ, x', s, κ, hf, hκ, rfl⟩

theorem valAt_generic [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (hb : IsBasis x b) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (T T' : Fin x.P.g × Fin (n ^ x.P.g) → Ω) (a a' : Ω)
    (hT : AlgebraicIndependent K (Sum.elim T T')) (h : ValAt b l l' al Ω T a) (h' : ValAt b l l' al Ω T' a') :
    a = a' := by
  obtain ⟨x1, s1, κ1, h1, hk1, rfl⟩ := h
  obtain ⟨x2, s2, κ2, h2, hk2, rfl⟩ := h'
  obtain ⟨φ, w, hg, b', H, hb', hs1⟩ := id h1
  choose s3 hs3 using fun i : Fin x1.P.g => exists_coords x1 b' (fun k => T' (i.cast hg, k))
  have h3 : Framed b (algebraMap K Ω) T' x1 s3 := ⟨φ, w, hg, b', H, hb', hs3⟩
  have h3' : Framed b ((RingHom.id Ω).comp (algebraMap K Ω)) (RingHom.id Ω ∘ T') x1 s3 := by
    simpa only [RingHom.id_comp, RingHom.coe_id, Function.id_comp] using h3
  have hk3 := h2.kaVal hL hA h3' hk2
  have hinj : Function.Injective
      (fun p : Fin x1.P.g × Fin (n ^ x.P.g) => ((p.1.cast hg, p.2) : Fin x.P.g × Fin (n ^ x.P.g))) :=
    fun p q hpq => Prod.ext (Fin.ext (congrArg (fun r => (r.1 : ℕ)) hpq)) (congrArg (fun r => r.2) hpq)
  have hind := hT.comp _ (Sum.map_injective.mpr ⟨hinj, hinj⟩)
  rw [Sum.elim_comp_map] at hind
  have e := GlobalTheory.T.keyInvariant_eq_of_independent_generic_tuples hL K Ω x x1 φ w n l l' al b b' (fun p => T (p.1.cast hg, p.2))
    (fun p => T' (p.1.cast hg, p.2)) s1 s3 κ1 _ hA H hb hb' hind hs1 hs3 hk1 hk3
  rw [e]
  rfl

theorem valAt_lift [CharZero K] (hL : Out.Laws) (hA : admitted x.P.g n l l' al) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra K O] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (r : O →ₐ[K] Ω)
    (T : Fin x.P.g × Fin (n ^ x.P.g) → O) (a : Ω) (hr : RingHom.ker r = IsLocalRing.maximalIdeal O)
    (h : ValAt b l l' al Ω (r ∘ T) a) :
    ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O') (_ : Algebra K O')
      (j : O →ₐ[K] O') (r' : O' →ₐ[K] Ω) (u : O'), Function.Injective j ∧ r'.comp j = r ∧
        ValAt b l l' al O' (j ∘ T) u := by
  obtain ⟨xΩ, sΩ, κ, hΩ, hκ, rfl⟩ := h
  obtain ⟨xO, sO, hO⟩ := exists_framed b (algebraMap K O) T
  have hΩ' : Framed b ((r : O →+* Ω).comp (algebraMap K O)) ((r : O →+* Ω) ∘ T) xΩ sΩ := by
    rw [r.comp_algebraMap]; exact hΩ
  obtain ⟨φ, w, hg, H, hs⟩ := hO.via hΩ'
  obtain ⟨z, ch, _, _, _, _, _, _, _, hz, _⟩ := id hκ
  have hAO : admitted xO.P.g n l l' al := by rw [hO.g_eq]; exact hA
  have hu : IsUnit ((degProd xO.P.g n l l' : ℕ) : O) := by
    have h0 : ((degProd xO.P.g n l l' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (degProd_ne_zero hAO)
    have := (IsUnit.mk0 _ h0).map (algebraMap K O)
    rwa [map_natCast] at this
  obtain ⟨O', i1, i2, i3, j, r', x', φ', w', hg', s', u, hj, -, hr', H', hs', hu'⟩ :=
    GlobalTheory.T.exists_keyInvariant_after_dvr_extension hL O Ω (r : O →+* Ω) xO xΩ φ w n l l' al _ hg sO sΩ z ch hr hAO hu H hs hz
  letI : Algebra K O' := (j.comp (algebraMap K O)).toAlgebra
  let jA : O →ₐ[K] O' := { toRingHom := j, commutes' := fun c => rfl }
  let rA : O' →ₐ[K] Ω :=
    { toRingHom := r', commutes' := fun c => by
        show r' (j (algebraMap K O c)) = algebraMap K Ω c
        rw [← RingHom.comp_apply, hr']
        exact r.commutes c }
  refine ⟨O', i1, i2, i3, inferInstance, jA, rA, (u : O'), hj, ?_, ?_⟩
  · ext c
    show r' (j c) = r c
    rw [← RingHom.comp_apply, hr']
    rfl
  · obtain ⟨x'', s'', h''⟩ := exists_framed b (algebraMap K O') (jA ∘ T)
    have h2 : Framed b (j.comp (algebraMap K O)) (j ∘ T) x'' s'' := h''
    obtain ⟨φ2, w2, hg2, H2, hs2⟩ := hO.via h2
    have H2' : KeyVia x'' xO ((RingHom.id O').comp j) φ2 w2 := by rw [RingHom.id_comp]; exact H2
    obtain ⟨φ3, w3, H3, -, hsec⟩ := GlobalTheory.KaLift.keyVia_cancel H' H2'
    have hg3 : x''.P.g = x'.P.g := hg2.trans hg'.symm
    have hs3 : ∀ i, SecVia x'' x' φ3 w3 (s'' i) (s' (i.cast hg3)) := by
      intro i
      have h1 := hs' (i.cast hg3)
      have e : (i.cast hg3).cast hg' = i.cast hg2 := Fin.ext rfl
      rw [e] at h1
      exact hsec n (sO (i.cast hg2)) (s' (i.cast hg3)) (s'' i) h1 (hs2 i)
    have hA' : admitted x'.P.g n l l' al := by rw [hg']; exact hAO
    have hk := GlobalTheory.T.keyInvariant_baseChange hL O' O' x' x'' (RingHom.id O') φ3 w3 n l l' al hg3 s' s'' u hA' H3 hs3 hu'
    exact ⟨x'', s'', _, h'', hk, rfl⟩

theorem kaVal_independent : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted x.P.g n l l' al → ∃ κ : Kˣ, (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyPB x' x f → KaVal x' n l l' al s' κ' → (κ' : K') = f κ) ∧ ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (f : K →+* K') (x' : KeyIn K') (φ : _) (w : _) (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyVia x' x f φ w ∧ KaVal x' n l l' al s' κ' := by
  intro hL K _ _ _ x n l l' al hA
  obtain ⟨⟨b, hb⟩, hpull⟩ := GlobalTheory.KeyBasis.main hL K x n (by have := hA.1; omega)
  obtain ⟨κ0, hall, hgen⟩ := GlobalTheory.GenericValue.exists_value (K := K)
    (fun (R : Type) [CommRing R] [Algebra K R] (T : Fin x.P.g × Fin (n ^ x.P.g) → R) (a : R) =>
      ValAt b l l' al R T a)
    (valAt_map (b := b) hL hA) (valAt_unique (b := b) hL hA) (exists_valAt (b := b) hL hA hb)
    (valAt_generic (b := b) hL hA hb) (valAt_lift (b := b) hL hA)
  obtain ⟨xG, sG, κG, hfG, hkG, hG⟩ := hgen
  have hκ0 : κ0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hG
    exact κG.ne_zero hG.symm
  refine ⟨Units.mk0 κ0 hκ0, ?_, ?_⟩
  · intro K' _ _ f x' s' κ' hx' hk'
    letI : Algebra K K' := f.toAlgebra
    obtain ⟨φ, w, H⟩ := (GlobalTheory.KeyVia.main K K' x x' f).1.1 hx'
    obtain ⟨_, hg, _⟩ := id H
    have M := (GlobalTheory.KeyVia.main K K' x x' f).2 φ w H
    choose b' hb' _ using fun k => M.1 n (b k)
    have hbas : IsBasis x' b' := (hpull b hb K' f x' φ w b' H hb')
    choose c hc _ using fun i : Fin x.P.g => hbas (s' (i.cast hg.symm))
    have hf : Framed b (algebraMap K K') (fun p => c p.1 p.2) x' s' := by
      refine ⟨φ, w, hg, b', H, hb', fun i => ?_⟩
      have e : (i.cast hg).cast hg.symm = i := Fin.ext rfl
      have h1 := hc (i.cast hg)
      rw [e] at h1
      exact h1
    have h2 := hall K' (fun p => c p.1 p.2) κ' ⟨x', s', κ', hf, hk', rfl⟩
    rw [h2, Units.val_mk0]
    rfl
  · obtain ⟨φ, w, hg, b', H, -, -⟩ := hfG
    exact ⟨_, inferInstance, inferInstance, algebraMap K _, xG, φ, w, sG, κG, H, hkG⟩

end GlobalTheory.KaIndep
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyInvariant_independent_of_sections : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ), admitted x.P.g n l l' al → ∃ κ : Kˣ, (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyPB x' x f → KaVal x' n l l' al s' κ' → (κ' : K') = f κ) ∧ ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (f : K →+* K') (x' : KeyIn K') (φ : _) (w : _) (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ), KeyVia x' x f φ w ∧ KaVal x' n l l' al s' κ' := by
  atlas_forward_decl GlobalTheory.KaIndep.kaVal_independent
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.KaExists

open GlobalTheory.KeyGalDesc (g_eq exists_keyPB_pair)

theorem exists_coords {R : Type} [CommRing R] (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) :
    ∃ s : RR x l, Coords x b c s.f := by
  refine ⟨⟨fun i => ∑ k, cst x.P.A.hom (x.P.L.U i) (c k) * (show Γ(x.P.A.left, x.P.L.U i) from (b k).f i),
    fun i j => ?_⟩, fun i => rfl⟩
  refine (map_sum _ _ _).trans (Eq.trans ?_ (congrArg _ (map_sum _ _ _)).symm)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine (map_mul _ _ _).trans (Eq.trans ?_ (congrArg _ (map_mul _ _ _)).symm)
  exact (congrArg₂ (· * ·) ((rs_cst _ _ _).trans (rs_cst _ inf_le_right _).symm) ((b k).compat i j)).trans
    (mul_left_comm _ _ _)

theorem exists_kaVal_of_keyPB (hL : Out.Laws) {R R' : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing R'] [IsLocalRing R'] {x : KeyIn R} {x' : KeyIn R'} {f : R →+* R'} {n l l' : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} {s : Fin x.P.g → RR x n} {κ : Rˣ} (hA : admitted x.P.g n l l' al)
    (h : KeyPB x' x f) (hκ : KaVal x n l l' al s κ) :
    ∃ (s' : Fin x'.P.g → RR x' n) (κ' : R'ˣ), KaVal x' n l l' al s' κ' ∧ (κ' : R') = f κ := by
  have hg := g_eq h
  obtain ⟨φ, w, hv⟩ := (KeyVia.main R R' x x' f).1.1 h
  choose t ht using fun s : RR x n => (((KeyVia.main R R' x x' f).2 φ w hv).1 n s).exists
  exact ⟨fun i => t (s (i.cast hg)), _, GlobalTheory.T.keyInvariant_baseChange hL R R' x x' f φ w n l l' al hg s _ κ hA hv (fun i => ht _) hκ, rfl⟩

theorem exists_algebraicIndependent (K : Subfield ℂ) [Countable K] (I : Type) [Finite I] :
    ∃ T : I → ℂ, AlgebraicIndependent K T := by
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K ℂ
  have hK : Cardinal.mk K ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hst : Cardinal.mk I ≤ Cardinal.mk t := by
    refine le_of_not_gt fun hlt => ?_
    have h1 := IsAlgClosed.cardinal_le_max_transcendence_basis' _ ht
    have h2 : Cardinal.mk ℂ ≤ Cardinal.aleph0 :=
      h1.trans (max_le (max_le hK (hlt.le.trans Cardinal.mk_le_aleph0)) le_rfl)
    rw [Cardinal.mk_complex] at h2
    exact absurd h2 (not_le.mpr Cardinal.aleph0_lt_continuum)
  obtain ⟨e⟩ := hst
  exact ⟨_, ht.1.comp e e.injective⟩

theorem exists_extension_algebraicIndependent (k : Type) [Field k] (I : Type) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (T : I → Ω), AlgebraicIndependent k T := by
  let F := FractionRing (MvPolynomial I k)
  let f : MvPolynomial I k →ₐ[k] AlgebraicClosure F :=
    (IsScalarTower.toAlgHom k F (AlgebraicClosure F)).comp (IsScalarTower.toAlgHom k (MvPolynomial I k) F)
  exact ⟨AlgebraicClosure F, inferInstance, inferInstance, inferInstance, _,
    (MvPolynomial.algebraicIndependent_X I k).map' (f := f) fun _ _ h =>
      IsFractionRing.injective (MvPolynomial I k) F ((algebraMap F (AlgebraicClosure F)).injective h)⟩

theorem exists_kaVal_complex (hL : Out.Laws) (hD : KeyDesc) (x : KeyIn ℂ) {n l l' : ℕ}
    {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (hA : admitted x.P.g n l l' al) (hM : 1 ≤ degProd x.P.g n l l') :
    ∃ (s : Fin x.P.g → RR x n) (κ : ℂˣ), KaVal x n l l' al s κ := by
  obtain ⟨K, x₀, hK, h⟩ := hD ℂ x
  obtain ⟨φ, w, hv⟩ := (KeyVia.main _ _ x₀ x _).1.1 h
  obtain ⟨b, hb⟩ := (KeyBasis.main hL K x₀ n (le_trans (by norm_num) hA.1)).1
  choose t ht using fun s : RR x₀ n => (((KeyVia.main _ _ x₀ x _).2 φ w hv).1 n s).exists
  obtain ⟨T, hT⟩ := exists_algebraicIndependent K (Fin x.P.g × Fin (n ^ x₀.P.g))
  choose s hs using fun i => exists_coords x (fun j => t (b j)) (fun j => T (i, j))
  obtain ⟨d, z, ch, hz⟩ := GlobalTheory.T.generic_sections_meet_transversally hL K ℂ x₀ x φ w n b _ T s hA.1 hv hb (fun j => ht _) hT hs
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_keyInvariant_algClosed_transversal hL ℂ x n l l' al d s z ch hA (Nat.cast_ne_zero.2 (by omega)) hz
  exact ⟨s, κ, hκ⟩

theorem exists_kaVal_dvr (hL : Out.Laws) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (x : KeyIn R) {n l l' : ℕ} {al : ℕ → Matrix (Fin 4) (Fin 4) ℤ} (hA : admitted x.P.g n l l' al)
    (hM : IsUnit ((degProd x.P.g n l l' : ℕ) : R)) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (j : R →+* R')
      (x' : KeyIn R') (s' : Fin x'.P.g → RR x' n) (u : R'ˣ),
      Function.Injective j ∧ IsLocalHom j ∧ KeyPB x' x j ∧ KaVal x' n l l' al s' u := by
  classical
  let k := IsLocalRing.ResidueField R
  obtain ⟨Ω, _, _, _, T, hT⟩ := exists_extension_algebraicIndependent k (Fin x.P.g × Fin (n ^ x.P.g))
  let r : R →+* Ω := (algebraMap k Ω).comp (IsLocalRing.residue R)
  have hr : RingHom.ker r = IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.ker_residue]
    exact RingHom.ker_comp_of_injective _ (algebraMap k Ω).injective
  obtain ⟨O, _, _, _, j, r', -, hj, hloc, hcomp, hker, hS⟩ :=
    exists_complete_discreteValuationRing_with_residues R Ω r (Finset.univ.image T) hr
  choose T' hT' using fun q => hS (T q) (Finset.mem_image_of_mem T (Finset.mem_univ q))
  obtain ⟨b, hb⟩ := (KeyBasis.main hL R x n (le_trans (by norm_num) hA.1)).1
  have pull : ∀ {S : Type} [CommRing S] (f : R →+* S), ∃ (y : KeyIn S) (φ : _) (w : _) (c : Fin (n ^ x.P.g) → RR y n),
      KeyVia y x f φ w ∧ ∀ i, SecVia y x φ w (c i) (b i) := fun f => by
    obtain ⟨y, hy⟩ := exists_keyPB_ring x f
    obtain ⟨φ, w, hv⟩ := (KeyVia.main _ _ x y _).1.1 hy
    choose t ht using fun s : RR x n => (((KeyVia.main _ _ x y _).2 φ w hv).1 n s).exists
    exact ⟨y, φ, w, fun i => t (b i), hv, fun i => ht _⟩
  obtain ⟨xk, φk, wk, bk, hvk, hbk⟩ := pull (IsLocalRing.residue R)
  obtain ⟨xO, φO, wO, bO, hvO, hbO⟩ := pull j
  obtain ⟨xΩ, φΩ, wΩ, bΩ, hvΩ, hbΩ⟩ := pull r
  have pk := (KeyVia.main _ _ x xk _).1.2 ⟨_, _, hvk⟩
  have pO := (KeyVia.main _ _ x xO _).1.2 ⟨_, _, hvO⟩
  have gk := g_eq pk
  have gO := g_eq pO
  have gΩ := g_eq ((KeyVia.main _ _ x xΩ _).1.2 ⟨_, _, hvΩ⟩)
  obtain ⟨φ₁, w₁, hv₁, -, hs₁⟩ := KaLift.keyVia_cancel (f' := algebraMap k Ω) hvk hvΩ
  obtain ⟨φ₂, w₂, hv₂, -, hs₂⟩ := KaLift.keyVia_cancel (f' := r') hvO (hcomp ▸ hvΩ)
  have hbk' := (KeyBasis.main hL R x n (le_trans (by norm_num) hA.1)).2 b hb _ _ xk φk wk bk hvk hbk
  choose s hs using fun i : Fin xO.P.g => exists_coords xO bO (fun q => T' (i.cast gO, q))
  choose t ht using fun s : RR xO n => (((KeyVia.main _ _ xO xΩ _).2 φ₂ w₂ hv₂).1 n s).exists
  have g₂ : xΩ.P.g = xO.P.g := gΩ.trans gO.symm
  have hc : ∀ i : Fin xΩ.P.g, Coords xΩ bΩ (fun q => T (i.cast gΩ, q)) (t (s (i.cast g₂))).f := fun i => by
    have := ((KeyVia.main _ _ xO xΩ _).2 φ₂ w₂ hv₂).2.2 n _ bO bΩ _ _ _
      (fun q => hs₂ n _ _ _ (hbO q) (hbΩ q)) (ht (s (i.cast g₂))) (hs _)
    simpa only [hT', Fin.cast_cast] using this
  have gen : ∀ {m : ℕ} (e : xk.P.g = m) (bk : Fin (n ^ m) → RR xk n) (bΩ : Fin (n ^ m) → RR xΩ n)
      (T : Fin xΩ.P.g × Fin (n ^ m) → Ω) (s : Fin xΩ.P.g → RR xΩ n), IsBasis xk bk →
      (∀ q, SecVia xΩ xk φ₁ w₁ (bΩ q) (bk q)) → AlgebraicIndependent k T →
      (∀ i, Coords xΩ bΩ (fun q => T (i, q)) (s i).f) → ∃ (d : ℕ) (z : Fin d → Pt xΩ) (ch : Fin d → xΩ.P.L.ι),
        EtZ xΩ s z ch := fun e bk bΩ T s h₁ h₂ h₃ h₄ => by
    subst e
    exact GlobalTheory.T.generic_sections_meet_transversally hL k Ω xk xΩ φ₁ w₁ n bk bΩ T s hA.1 hv₁ h₁ h₂ h₃ h₄
  obtain ⟨d, z, ch, hz⟩ := gen gk bk bΩ (T ∘ Prod.map (Fin.cast gΩ) id) (fun i => t (s (i.cast g₂))) hbk'
    (fun q => hs₁ n _ _ _ (hbk q) (hbΩ q))
    (hT.comp _ ((Fin.cast_injective gΩ).prodMap Function.injective_id)) hc
  obtain ⟨O', _, _, _, j', -, x', φ', w', -, s', u, hj', hloc', -, hv', -, hu⟩ :=
    GlobalTheory.T.exists_keyInvariant_after_dvr_extension hL O Ω r' xO xΩ φ₂ w₂ n l l' al d g₂ s _ z ch hker (gO ▸ hA)
      (by rw [gO]; simpa using hM.map j) hv₂ (fun i => ht _) hz
  exact ⟨O', inferInstance, inferInstance, inferInstance, j'.comp j, x', s', u, hj'.comp hj, inferInstance,
    keyPB_trans _ _ _ x xO x' _ _ pO ((KeyVia.main _ _ xO x' _).1.2 ⟨_, _, hv'⟩), hu⟩

theorem kaSt : Out.Laws → ThetaUnifAV → GlobalTheory.TorusAlgebraic → KeyDesc → KaSt := by
  intro hL hU hT hD g p hg hp
  classical
  obtain ⟨n, l, l', al, hA, hpM, hM, hc⟩ := exists_admissibleKeyNumericalData_prime_to g p hg hp
  refine ⟨kaExp g n l l', degProd g n l l', hc, hM, hpM, ?_⟩
  have ex : ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K), ∃ κ : Kˣ, x.P.g = g →
      (∀ (K' : Type) [Field K'] [IsAlgClosed K'] (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n) (κ' : K'ˣ),
        KeyPB x' x f → KaVal x' n l l' al s' κ' → (κ' : K') = f κ) ∧
      ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (f : K →+* K') (x' : KeyIn K') (s' : Fin x'.P.g → RR x' n)
        (κ' : K'ˣ), KeyPB x' x f ∧ KaVal x' n l l' al s' κ' := fun K _ _ _ x => by
    by_cases hx : x.P.g = g
    · obtain ⟨κ, h₁, K', _, _, f, x', φ, w, s', κ', h₂, h₃⟩ := GlobalTheory.T.keyInvariant_independent_of_sections hL K x n l l' al (hx ▸ hA)
      exact ⟨κ, fun _ => ⟨h₁, K', inferInstance, inferInstance, f, x', s', κ',
        (KeyVia.main _ _ x x' _).1.2 ⟨_, _, h₂⟩, h₃⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose ka hka using ex
  have self : ∀ (K : Type) [Field K] [CharZero K] [IsAlgClosed K] (x : KeyIn K) (s : Fin x.P.g → RR x n) (κ : Kˣ),
      x.P.g = g → KaVal x n l l' al s κ → (ka K x : K) = κ := fun K _ _ _ x s κ hx h =>
    ((hka K x hx).1 K _ x s κ (keyPB_id _ x) h).symm
  refine ⟨fun K _ _ _ x => ka K x, ?_, ?_, ?_, ?_⟩
  · intro K _ _ _ P hg rig hr th hth v hv th' hth' v' hv' a Mx hP ha hMx
    obtain ⟨h₁, K', _, _, f, x', s', κ', hx', hκ'⟩ := hka K ⟨P, hg, rig, hr, th, hth, v, hv⟩ hP
    obtain ⟨Q, hg₁, rig₁, hr₁, th₁, hth₁, v₁, hv₁, th₁', hth₁', v₁', hv₁', N, p₁, p₂, ha₁, hN, hd⟩ :=
      exists_keyPB_pair f P hg rig hr th hth v hv th' hth' v' hv' a Mx ha hMx
    have hQ : Q.g = g := (g_eq p₁).trans hP
    obtain ⟨s₁, κ₁, hκ₁, -⟩ := exists_kaVal_of_keyPB hL (((g_eq hx').trans hP).symm ▸ hA)
      (KeyCancel.keyPB_cancel _ _ _ _ x' _ f (RingHom.id K') hx' p₁) hκ'
    obtain ⟨κ₂, hκ₂, e⟩ := KaScale.kaVal_scale K' Q hg₁ rig₁ hr₁ th₁ hth₁ v₁ hv₁ th₁' hth₁' v₁' hv₁' (f a) N n l l' al
      s₁ κ₁ (hQ ▸ hA) ha₁ hN hκ₁
    rw [h₁ K' f _ s₁ κ₁ p₁ hκ₁, (hka K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ hP).1 K' f
      ⟨Q, hg₁, rig₁, hr₁, th₁', hth₁', v₁', hv₁'⟩ s₁ κ₂ p₂ hκ₂, hd, hQ] at e
    apply f.injective
    simpa only [map_mul, map_pow] using e
  · intro K K' _ _ _ _ _ _ f x x' hx h
    obtain ⟨h₁, K'', _, _, f', x'', s, κ, hx'', hκ⟩ := hka K' x' ((g_eq h).trans hx)
    exact f'.injective ((h₁ K'' f' x'' s κ hx'' hκ).symm.trans
      ((hka K x hx).1 K'' _ x'' s κ (keyPB_trans _ _ _ x x' x'' _ _ h hx'') hκ))
  · intro R _ _ _ _ x hx hu
    obtain ⟨R', _, _, _, j, x', s', u, hj, hloc, hx', hκ⟩ := exists_kaVal_dvr hL R x (hx ▸ hA) (hx ▸ hu)
    refine ⟨R', inferInstance, inferInstance, inferInstance, j, u, hj, hloc, fun K _ _ _ f xK h => ?_⟩
    obtain ⟨s, κ, h₁, h₂⟩ := exists_kaVal_of_keyPB hL (((g_eq hx').trans hx).symm ▸ hA)
      (KeyCancel.keyPB_cancel _ _ _ x x' xK j f hx' h) hκ
    exact (self K xK s κ ((g_eq h).trans hx) h₁).trans h₂
  · intro a b hab
    have wit : ∀ q ∈ Key.phDom g, ∃ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g),
        Wit x h u (per q) a b := fun q hq => by
      obtain ⟨x, h, hx⟩ := KeyOfPeriod.exists_keyIn_normalAt hU hT g (per q) a b hg hq.1 hq.2 hab
      obtain ⟨u, hu⟩ := (normalAt_iff_wit g x h _ a b).1 hx
      exact ⟨x, h, u, hu⟩
    have loc : ∀ q ∈ Key.phDom g, ∃ (W : Set (Fin g → Fin g → ℂ)) (V : (Fin g → Fin g → ℂ) → ℂ), IsOpen W ∧ q ∈ W ∧
        W ⊆ Key.phDom g ∧ DifferentiableOn ℂ V W ∧ ∀ q' ∈ W, ∀ (x : KeyIn ℂ) (h : x.P.g = g)
          (u : HolUnif x.P.A x.P.L g), Wit x h u (per q') a b → (ka ℂ x : ℂ) = V q' := fun q hq => by
      obtain ⟨x₀, h₀, u₀, hw⟩ := wit q hq
      obtain ⟨s₀, κ₀, hκ₀⟩ := exists_kaVal_complex hL hD x₀ (h₀ ▸ hA) (h₀ ▸ hM)
      obtain ⟨W, V, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.koszulInvariant_locally_holomorphic_periodMatrix hL hU g n l l' al a b q x₀ h₀ u₀ s₀ κ₀ hab hA hq hw hκ₀
      refine ⟨W, V, h₁, h₂, h₃, h₄, fun q' hq' x h u hx => ?_⟩
      obtain ⟨s, κ, hκ, e⟩ := h₅ q' hq' x h u hx
      exact (self ℂ x s κ h hκ).trans e
    have sym : ∀ τ : Matrix (Fin g) (Fin g) ℂ, τ.IsSymm → per (Matrix.of.symm τ) = τ := fun τ hτ => by
      ext i j
      have := hτ.apply i j
      simp [per, Key.phSym, this]
      ring
    have val : ∀ τ : Matrix (Fin g) (Fin g) ℂ, ∃ c : ℂ, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g),
        Wit x h u τ a b → (ka ℂ x : ℂ) = c := fun τ => by
      by_cases hτ : τ.IsSymm ∧ (τ.map Complex.im).PosDef
      · obtain ⟨W, V, -, h₂, -, -, h₅⟩ := loc (Matrix.of.symm τ) (by
          show per (Matrix.of.symm τ) ∈ ReciprocityTheory.PTheta.SiegelH (Fin g)
          rw [sym τ hτ.1]
          exact hτ)
        exact ⟨_, fun x h u hx => h₅ _ h₂ x h u ((sym τ hτ.1).symm ▸ hx)⟩
      · exact ⟨0, fun x h u hx => absurd ⟨hx.1, hx.2.1⟩ hτ⟩
    choose U hUv using val
    refine ⟨U, fun q hq => ?_, fun x h τ hτ => ?_⟩
    · obtain ⟨W, V, h₁, h₂, h₃, h₄, h₅⟩ := loc q hq
      refine ((h₄.differentiableAt (h₁.mem_nhds h₂)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [h₁.mem_nhds h₂] with q' hq'
      obtain ⟨x, h, u, hx⟩ := wit q' (h₃ hq')
      exact (hUv _ x h u hx).symm.trans (h₅ q' hq' x h u hx)
    · obtain ⟨u, hu⟩ := (normalAt_iff_wit g x h τ a b).1 hτ
      exact hUv _ x h u hu

end GlobalTheory.KaExists
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralKeyInvariantRule_charZero : Out.Laws → ThetaUnifAV → GlobalTheory.TorusAlgebraic → KeyDesc → KaSt := by
  atlas_forward_decl GlobalTheory.KaExists.kaSt
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyPow

theorem keyFormulaPow_of_keyRule :
    ThetaUnifAV → ∀ N : ℕ → ℕ, (∀ g, 1 ≤ N g) → GlobalTheory.KeyPow.KeyRule N 1 GlobalTheory.KeyPow.charHalf → GlobalTheory.KeyFormulaPow := by
  rintro hT N hN ⟨κ, hH, hF, hU, hK⟩
  refine ⟨N, hN, κ, fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M =>
      hH K P hg rig hr th hth v hv th' hth' v' hv' a M hg,
    fun K K' _ _ _ _ f x x' => hF K K' f x x' x.g_pos,
    fun R K _ _ _ _ _ _ _ x xK => hU R K x xK x.g_pos,
    fun x u τ a b h₁ h₂ ha hb h₃ h₄ h₅ h₆ =>
      hK x τ a b x.g_pos ⟨ha, hb⟩ ((normalAt_one_iff x τ a b).2 ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩), ?_⟩
  intro x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  obtain ⟨u', τ, M, a, b, c, k₁, k₂, ha, hb, k₃, k₄, hc, k₅, hM, k₆, hn⟩ :=
    keyIn_normal_form_and_archimedean_constant hT x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have hv := value_at_normalForm N 1 (κ ℂ) x.P.g a b x.g_pos (hH ℂ)
    (fun y h τ' hy => hK y τ' _ _ y.g_pos ⟨fun i => ha _, fun i => hb _⟩ hy) x rfl τ M c hc hM
    ⟨u', k₁, k₂, k₃, k₄, k₅, k₆⟩
  rw [hv, norm_pow, pow_mul nth, pow_mul nη, ← mul_pow, ← mul_pow, hn, ← pow_mul]



end GlobalTheory.KeyPow
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTop

theorem exists_keyRule_charHalf :
    Out.Laws → ThetaUnifAV → Key.Chi.InversionStatement → Key.PhHoloStatement → GlobalTheory.TorusAlgebraic →
      ∃ N : ℕ → ℕ, (∀ g, 1 ≤ N g) ∧ KeyRule N 1 charHalf := by
  intro hL hT hI hP hTor
  have hD : KeyDesc := (GlobalTheory.T.keyData_descend_countable_subrings hL).2
  exact GlobalTheory.T.thetaKeyRule_exists_of_algebraic_invariants hL hT hI hP hTor (GlobalTheory.T.exists_integralKeyInvariantRule_charZero hL hT hTor hD) hD

end GlobalTheory.KeyTop
end
