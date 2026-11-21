import Mathlib
import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CardFunLevQ
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIdem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TorsionIsotropicCommutatorPairing
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUnitaryOfSelfDual
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPrincipalIdealRingLoc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullbackStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InZhIffKillsAdapted
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqOfSqEqOfOdd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ReachedSectionRegularOnIntegralModelStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralChartFormalBiextensionGaugeBoundStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupPointsOfIntegralChartSpecStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SplitKernelFormalGroupOfRationalTorsion
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.KillsFormalPointsIffMemCoordinateKernel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumHarmonicValuesFormalKernelSimilitude
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlaceB
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TorsionRationalOverFiniteExtensionLevelStructureStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslateMulOfCoprimeOrders
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNorm
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MemRangeOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsotropicGroupPrimaryDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortBoundOfTrivAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfCastDvd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsIntegralZpowOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EmbEqOfInPsi
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightOnDatum

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.AdaptExists

theorem mem_std {E : Type} [Field E] {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = v i := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one]

theorem single_mem {E : Type} [Field E] {n : ℕ} (j : Fin n) : (Pi.single j (1 : E) : Fin n → E) ∈ stdLat E n := by
  rw [mem_std]
  intro i
  by_cases h : i = j
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [h]⟩

theorem nat_smul_mem {E : Type} [Field E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (k : ℕ) {v : Fin n → E}
    (hv : v ∈ L) : (k : E) • v ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact L.toAddSubmonoid.nsmul_mem hv k

theorem exists_cols {E : Type} [Field E] {n : ℕ} (c : Fin n → Fin n → E) (hc : ∀ j, c j ∈ stdLat E n) :
    ∃ q : Matrix (Fin n) (Fin n) (𝓞 E), ∀ i j, algebraMap (𝓞 E) E (q i j) = c j i := by
  choose a ha using fun j => (mem_std (c j)).1 (hc j)
  exact ⟨Matrix.of fun i j => a j i, fun i j => ha j i⟩

theorem exists_adapt (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ) (Λ : GenLat E n)
    (N M ℓ : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M) (hl : ℓ.Prime) :
    ∃ A : Adapt Λ N ℓ, IsSim H (A.p * A.q) ((A.k * N) ^ 2) := by
  obtain ⟨hodd, -, hN⟩ := hL
  have hN0 : 0 < N := hodd.pos
  have hm : 0 < 2 * ℓ := Nat.mul_pos two_pos hl.pos
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := RingOfIntegers.coe_injective
  obtain ⟨k₂, ga, hk₂, hun, hin, hon⟩ := GlobalTheory.AdaptUnitary.exists_unitary_adapted E H n Λ N hU hN0 (hN.trans inf_le_left) (2 * ℓ) hm
  obtain ⟨k₁, g, hk₁, -, hcols, hsp⟩ := LocBasis.exists_matrix_primeTo E n Λ.Ln N hN0 inf_le_right hN (2 * ℓ) hm
  set G := g.map (algebraMap (𝓞 E) E) with hG
  have hNe : ∀ j : Fin n, (N : E) • (Pi.single j (1 : E) : Fin n → E) ∈ Λ.Ln := by
    intro j
    have h := hN (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) (single_mem (E := E) j))
    rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h
  choose v hv hve using fun j => hsp _ (hNe j)
  obtain ⟨q, hq⟩ := exists_cols v hv
  obtain ⟨p, hp⟩ := exists_cols (fun j => (k₂ : E) • ga.mulVec (G.mulVec (Pi.single j 1)))
    (fun j => hin _ (hcols _ (single_mem j)).1)
  have hP : p.map (algebraMap (𝓞 E) E) = (k₂ : E) • (ga * G) := by
    ext i j
    rw [Matrix.map_apply, hp, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  have hGQ : G * q.map (algebraMap (𝓞 E) E) = ((k₁ * N : ℕ) : E) • (1 : Matrix (Fin n) (Fin n) E) := by
    ext i j
    have h := congrFun (hve j) i
    simp only [Matrix.mul_apply, Matrix.map_apply, hq]
    simp only [Matrix.mulVec, dotProduct] at h
    rw [← h]
    simp [Matrix.one_apply, Pi.single_apply]
  have hprod : (p * q).map (algebraMap (𝓞 E) E) = ((k₁ * k₂ * N : ℕ) : E) • ga := by
    rw [Matrix.map_mul, hP, Matrix.smul_mul, Matrix.mul_assoc, hGQ, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    push_cast
    ring
  have hk : Nat.Coprime (k₁ * k₂) (2 * ℓ) := Nat.Coprime.mul_left hk₁ hk₂
  refine ⟨{
    k := k₁ * k₂, k₁ := k₁, ga := ga, p := p, q := q, g := g
    odd := (Nat.coprime_two_right).1 (Nat.Coprime.coprime_mul_right_right hk)
    cop := Nat.Coprime.coprime_mul_left_right hk
    cop₁ := Nat.Coprime.coprime_mul_left_right hk₁
    unitary := hun
    into := ?_
    onto := ?_
    prod := hprod
    cols := hcols
    spans := hsp
    gq := ?_ }, ?_⟩
  · intro w hw
    rw [Nat.cast_mul, mul_smul]
    exact nat_smul_mem _ _ (hin w hw)
  · intro w hw
    obtain ⟨u, hu, e⟩ := hon w hw
    exact ⟨(k₁ : E) • u, nat_smul_mem _ _ hu, by rw [Nat.cast_mul, mul_smul, e, Matrix.mulVec_smul]⟩
  · apply Matrix.map_injective hinj
    show (g * q).map _ = Matrix.map _ _
    rw [Matrix.map_mul, hGQ]
    ext i j
    by_cases h : i = j <;> simp [h]
  · intro j k
    apply hinj
    have he : ∀ a b, algebraMap (𝓞 E) E ((p * q) a b) = ((k₁ * k₂ * N : ℕ) : E) * ga a b :=
      fun a b => congrFun (congrFun hprod a) b
    have hb : ∀ a : 𝓞 E, algebraMap (𝓞 E) E (H.bar a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := H.bar_eq
    show algebraMap (𝓞 E) E (∑ i, H.bar ((p * q) i j) * (p * q) i k) =
      algebraMap (𝓞 E) E (if j = k then (((k₁ * k₂ * N) ^ 2 : ℕ) : 𝓞 E) else 0)
    rw [map_sum]
    simp only [map_mul (algebraMap (𝓞 E) E), hb, he, map_mul (IsCMField.complexConj E), map_natCast]
    have : ∀ i, ((k₁ * k₂ * N : ℕ) : E) * IsCMField.complexConj E (ga i j) * (((k₁ * k₂ * N : ℕ) : E) * ga i k) =
        ((k₁ * k₂ * N : ℕ) : E) ^ 2 * (IsCMField.complexConj E (ga i j) * ga i k) := fun i => by ring
    simp only [this]
    rw [← Finset.mul_sum, hun]
    split_ifs <;> simp

end GlobalTheory.PlaceInt.AdaptExists
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_similitude_data_at_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ), Λ.Unimod → Λ.LevOK N M → ℓ.Prime → ∃ A : Adapt Λ N ℓ, IsSim H (A.p * A.q) ((A.k * N) ^ 2) := by
  atlas_forward_decl GlobalTheory.PlaceInt.AdaptExists.exists_adapt
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.CoreTrace

section Comb

theorem sum_comp_hom {A B K : Type} [Group A] [Group B] [Fintype A] [CommRing K] (φ : A →* B) [Fintype φ.range]
    (g : B → K) : ∑ x : A, g (φ x) = (Nat.card φ.ker : K) * ∑ h : φ.range, g h := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := φ.rangeRestrict), Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => g h) (fun x hx => by
    rw [← (Finset.mem_filter.1 hx).2]; rfl), Finset.sum_const, nsmul_eq_mul]
  congr 2
  obtain ⟨x, rfl⟩ := φ.rangeRestrict_surjective h
  rw [← Nat.card_congr (φ.fiberEquivKer x), ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun a => by simp [Subtype.ext_iff])

theorem sum_cosets {A K : Type} [CommGroup A] [Fintype A] [Field K] [CharZero K] (W₀ W₁ : Subgroup A) [Fintype W₁]
    (f : A → K) (hf : ∀ x, ∀ w ∈ W₀, f (x * w) = f x) (S : K → Prop)
    (hS : ∀ (I : Type) (t : Finset I) (z : I → K), (∀ i ∈ t, S (z i)) → S (∑ i ∈ t, z i)) (s d : K)
    (h : ∀ x, ∃ z, S z ∧ s * ∑ α : W₁, f (α * x) = (Nat.card {α : W₁ // (α : A) ∈ W₀} : K) * d * z) :
    ∃ z, S z ∧ s * ∑ x, f x = (Nat.card W₀ : K) * d * z := by
  classical
  choose z hz hz' using h
  let g : A ⧸ W₀ → K := fun c => f c.out
  have hg : ∀ x : A, g (x : A ⧸ W₀) = f x := fun x => by
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W₀ x
    simp only [g, hw, hf x w w.2]
  let φ : W₁ →* A ⧸ W₀ := (QuotientGroup.mk' W₀).comp W₁.subtype
  have hker : Nat.card φ.ker = Nat.card {α : W₁ // (α : A) ∈ W₀} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun α => by simp [φ, MonoidHom.mem_ker])
  have hne : (Nat.card φ.ker : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h1 : ∀ c : A ⧸ W₀, s * ∑ h : φ.range, g (c * h) = d * z c.out := fun c => by
    apply mul_left_cancel₀ hne
    rw [mul_left_comm, ← sum_comp_hom φ (fun b => g (c * b)), ← _root_.mul_assoc, hker, ← hz']
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← hg, QuotientGroup.mk_mul, QuotientGroup.out_eq', _root_.mul_comm]; rfl
  refine ⟨∑ c : (A ⧸ W₀) ⧸ φ.range, z c.out.out, hS _ _ _ fun c _ => hz _, ?_⟩
  have h2 : ∑ x, f x = (Nat.card W₀ : K) * ∑ c : A ⧸ W₀, g c := by
    have := sum_comp_hom (QuotientGroup.mk' W₀) g
    rw [QuotientGroup.ker_mk'] at this
    simp only [QuotientGroup.mk'_apply, hg] at this
    rw [this]
    congr 1
    exact Fintype.sum_bijective (fun c : (QuotientGroup.mk' W₀).range => (c : A ⧸ W₀))
      ⟨Subtype.val_injective, fun c => ⟨⟨c, QuotientGroup.mk'_surjective W₀ c⟩, rfl⟩⟩ _ g fun _ => rfl
  have h3 : ∑ c : A ⧸ W₀, g c = ∑ c : (A ⧸ W₀) ⧸ φ.range, ∑ h : φ.range, g (c.out * h) := by
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_bijective (fun p : ((A ⧸ W₀) ⧸ φ.range) × φ.range => p.1.out * p.2) ⟨?_, fun c => ?_⟩ _ _
      fun _ => rfl
    · rintro ⟨c, h⟩ ⟨c', h'⟩ hc
      obtain rfl : c = c' := by
        have := congrArg (QuotientGroup.mk (s := φ.range)) hc
        simpa only [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.mk_mul_of_mem _ h'.2,
          QuotientGroup.out_eq'] using this
      rw [Subtype.ext (mul_left_cancel hc : (h : A ⧸ W₀) = h')]
    · obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul φ.range c
      exact ⟨(c, w⁻¹), by simp [hw]⟩
  rw [h2, h3, mul_left_comm, Finset.mul_sum, Finset.sum_congr rfl fun c _ => h1 _, ← Finset.mul_sum, _root_.mul_assoc]
end Comb

section Move
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {T : CDVR} {x : Sp T.Fr ⟶ Xo.X} {n k : ℕ}

theorem liftFun_mul {S : Scheme.{0}} (A : Over S) {U : Over S} (W : (U ⊗ A).left.Opens) (a b : Γ(U.left, ⊤)) :
    liftFun A W (a * b) = liftFun A W a * liftFun A W b := by
  simp only [liftFun, map_mul]

theorem liftFun_one {S : Scheme.{0}} (A : Over S) {U : Over S} (W : (U ⊗ A).left.Opens) :
    liftFun A W (1 : Γ(U.left, ⊤)) = 1 := by
  simp only [liftFun, map_one]

def Rel (F F' : Fin n → SecN Xo x k) : Prop :=
  ∃ r : Fin n → T.V, ∏ b, r b = 1 ∧ (∀ b, r b ^ k = 1) ∧ ∀ b j, (F' b).f j =
    liftFun Xo.univ.t.G _ (T := ptO Xo x) (toΓ T.Fr (algebraMap T.V T.Fr (r b))) * (F b).f j

theorem Rel.trans {F F' F'' : Fin n → SecN Xo x k} (h : Rel F F') (h' : Rel F' F'') : Rel F F'' := by
  obtain ⟨r, h1, h2, h3⟩ := h
  obtain ⟨r', h1', h2', h3'⟩ := h'
  refine ⟨fun b => r' b * r b, by rw [Finset.prod_mul_distrib, h1, h1', _root_.mul_one],
    fun b => by rw [mul_pow, h2, h2', _root_.mul_one], fun b j => ?_⟩
  rw [h3', h3, map_mul, map_mul, ← _root_.mul_assoc]
  congr 1
  exact (liftFun_mul _ _ _ _).symm

theorem Rel.symm (hk : 0 < k) {F F' : Fin n → SecN Xo x k} (h : Rel F F') : Rel F' F := by
  obtain ⟨r, h1, h2, h3⟩ := h
  refine ⟨fun b => r b ^ (k - 1), by rw [Finset.prod_pow, h1, one_pow],
    fun b => by rw [← pow_mul, _root_.mul_comm, pow_mul, h2, one_pow], fun b j => ?_⟩
  have e : toΓ T.Fr (algebraMap T.V T.Fr (r b ^ (k - 1))) * toΓ T.Fr (algebraMap T.V T.Fr (r b)) = 1 := by
    rw [← map_mul, ← map_mul, ← pow_succ, Nat.sub_add_cancel hk, h2, map_one, map_one]
  rw [h3, ← _root_.mul_assoc]
  refine (_root_.one_mul _).symm.trans ?_
  congr 1
  exact (liftFun_one _ _).symm.trans ((congrArg _ e.symm).trans (liftFun_mul _ _ _ _))

theorem rel_of_moves (hk : Odd k) (u u' : Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hu : ∀ b, u b ^ k = 1)
    (hu' : ∀ b, u' b ^ k = 1)
    (hiso : ∀ ε : Fin n → Γ((ptO Xo x).left, ⊤)ˣ,
      (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (u b) (u' b) (ε b)) → ∏ b, ε b = 1)
    {F F₁ F₂ F₃ : Fin n → SecN Xo x k} (h₁ : ∀ b, Moves Xo (u' b) (F b) (F₁ b))
    (h₂ : ∀ b, Moves Xo (u b) (F₁ b) (F₂ b)) (h₃ : ∀ b, Moves Xo (u b * u' b) (F b) (F₃ b)) : Rel F₃ F₂ := by
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have := UnivPol.isLocallyNoetherian Xo
  have hw : ∀ b, ∃ ε : Γ((ptO Xo x).left, ⊤)ˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (u b) (u' b) ε :=
    fun b => ((hLaw.weil Xo.X (UnivPol.pol Xo) k (ptO Xo x)).1 (u b) (u' b) (hu b) (hu' b)).exists
  choose ε hε using hw
  choose r hr hrk hF using fun b => moves_mul E H Dw l Xo T.Fr x k hk (u b) (u' b) (ε b) (hu b) (hu' b) (hε b)
  have hint : ∀ b, ∃ v : T.V, algebraMap T.V T.Fr v = r b := fun b =>
    IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow hk.pos (by rw [hrk]; exact isIntegral_one))
  choose v hv using hint
  have inj := IsFractionRing.injective T.V T.Fr
  have bij : Function.Bijective (toΓ T.Fr) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of T.Fr)).inv
  have h2 : (∏ b, r b) ^ 2 = 1 := by
    apply bij.1
    rw [map_pow, map_prod, ← Finset.prod_pow, map_one, Finset.prod_congr rfl fun b _ => hr b]
    exact (Units.coe_prod ε Finset.univ).symm.trans (congrArg Units.val (hiso ε hε))
  have hk' : (∏ b, r b) ^ k = 1 := by rw [← Finset.prod_pow]; exact Finset.prod_eq_one fun b _ => hrk b
  refine ⟨v, inj ?_, fun b => inj (by rw [map_pow, hv, hrk, map_one]), fun b j => ?_⟩
  · obtain ⟨t, rfl⟩ := hk
    rw [pow_succ, pow_mul, h2, one_pow, _root_.one_mul] at hk'
    rw [map_prod, map_one, ← hk']
    exact Finset.prod_congr rfl fun b _ => hv b
  · rw [hv]
    exact hF b _ _ _ _ (h₁ b) (h₂ b) (h₃ b) j
end Move

section Ker
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (U : Over Xo.X) {n : ℕ}

def kerSub (mu : Matrix (Fin n) (Fin n) (𝓞 E)) : Subgroup (Fin n → (U ⟶ Xo.univ.t.G)) where
  carrier := {u | Kills Xo mu u}
  one_mem' := by
    letI := ZPart.ptMod Xo U
    refine (ZPart.kills_iff Xo mu _).2 fun i => Finset.sum_eq_zero fun j _ => ?_
    exact smul_zero _
  mul_mem' {u u'} hu hu' := by
    letI := ZPart.ptMod Xo U
    refine (ZPart.kills_iff Xo mu _).2 fun i => ?_
    have h := (ZPart.kills_iff Xo mu _).1 hu i
    have h' := (ZPart.kills_iff Xo mu _).1 hu' i
    simp only [Pi.mul_apply, ofMul_mul, smul_add, Finset.sum_add_distrib, h, h', add_zero]
  inv_mem' {u} hu := by
    letI := ZPart.ptMod Xo U
    refine (ZPart.kills_iff Xo mu _).2 fun i => ?_
    have h := (ZPart.kills_iff Xo mu _).1 hu i
    simp only [Pi.inv_apply, ofMul_inv, smul_neg, Finset.sum_neg_distrib, h, neg_zero]

def primSub (ℓ : ℕ) : Subgroup (Fin n → (U ⟶ Xo.univ.t.G)) where
  carrier := {u | ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1}
  one_mem' b := ⟨0, one_pow _⟩
  mul_mem' {u u'} hu hu' b := by
    obtain ⟨i, hi⟩ := hu b
    obtain ⟨j, hj⟩ := hu' b
    refine ⟨i + j, ?_⟩
    rw [Pi.mul_apply, mul_pow, pow_add, pow_mul, hi, one_pow, _root_.mul_comm (ℓ ^ i), pow_mul, hj, one_pow,
      _root_.mul_one]
  inv_mem' {u} hu b := (hu b).imp fun j hj => by rw [Pi.inv_apply, inv_pow, hj, inv_one]

variable {Xo U}
theorem pow_eq_one_of_kills {mu mu' : Matrix (Fin n) (Fin n) (𝓞 E)} {m : ℕ}
    (h : mu' * mu = (m : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E))) {u : Fin n → (U ⟶ Xo.univ.t.G)}
    (hu : Kills Xo mu u) (b : Fin n) : u b ^ m = 1 := by
  letI := ZPart.ptMod Xo U
  have h1 := ((ZPart.kills_iff Xo mu u).1 hu).mul mu'
  rw [h] at h1
  have h2 := h1 b
  rwa [Finset.sum_eq_single b (fun j _ hj => by simp [Matrix.one_apply_ne hj.symm]) (by simp),
    Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, _root_.mul_one, ← ZPart.pow_iff] at h2

theorem pow_eq_one_of_coprime {A : Type} [Group A] {u : A} {k N ℓ j : ℕ} (hc : Nat.Coprime k ℓ)
    (h : u ^ (k * N) = 1) (hj : u ^ (ℓ ^ j) = 1) : u ^ N = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one] at *
  exact (Nat.Coprime.coprime_dvd_left hj (hc.symm.pow_left j)).dvd_of_dvd_mul_left h

theorem adj_mul {mu : Matrix (Fin n) (Fin n) (𝓞 E)} {m : ℕ} (h : IsSim H mu m) :
    (Matrix.of fun j i => H.bar (mu i j)) * mu = (m : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) := by
  ext j k
  have := h j k
  simp only [Matrix.mul_apply, Matrix.of_apply, this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp
end Ker

theorem exists_cpt {V : Type} [CommRing V] {d : ℕ} (v : Pt V 0 d) : ∃ δ : Fin d → V, cpt δ = v := by
  refine ⟨fun i => MvPowerSeries.constantCoeff (v i), funext fun i => ?_⟩
  ext m
  obtain rfl : m = 0 := Subsingleton.elim _ _
  simp [cpt]

end GlobalTheory.CoreTrace

namespace GlobalTheory
open CoreTrace

theorem sum_hv_primary_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (N k M k₁ : ℕ) (p q g : Matrix (Fin n) (Fin n) (𝓞 E)), Odd N → IsSim H (p * q) (N ^ 2) → N ^ 2 = k * M → Nat.Coprime k ℓ → AllRat Xo (xOf y) M → Nat.Coprime k₁ ℓ → g * q = ((k₁ * N : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → ∀ (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)), Function.Injective a → (∀ u : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ i, a i = u) ↔ (Kills Xo (p * q) u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1))) → (∀ i i' (ε : Fin n → Γ((ptO Xo (xOf y)).left, ⊤)ˣ), (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N ^ 2 : ℕ) : ℤ) (a i b) (a i' b) (ε b)) → ∏ b, ε b = 1) → ∀ (F : Fin n → SecN Xo (xOf y) (N ^ 2)) (G : J → Fin n → SecN Xo (xOf y) (N ^ 2)), (∀ b, Reach Xo (sOf1 y) (N ^ 2) (F b)) → (∀ b (u : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)), (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u (F b) (F b)) → (∀ i b, Moves Xo (a i b) (F b) (G i b)) → ∀ (P : MvPolynomial (LtN Dw n) c.F) (s : c.F), P ∈ HH c w n → MvPolynomial.map io (MvPolynomial.C s * pushL c ((p * q).map (algebraMap (𝓞 E) E)) P) ∈ FFV (Dw := Dw) T w n → letI := io.toAlgebra; ∃ z : T.Fr, ((-ρ : ℝ) : EReal) ≤ nval T.V e z ∧ io s * ∑ i, hv Xo c nab y.1 (N ^ 2) (G i) P = (Nat.card {i : J // Kills Xo q (a i)} : T.Fr) * io (∏ τ : E →+* ℂ, embK c τ p.det ^ Dw.mult τ) * z := by
  intro E _ _ _ H Dw l Xo c _ hbar T io y C hC nab hnab e ρ w n he hB ℓ hℓ hℓu N k M k₁ p q g hN hsim hkM hk hM hk₁ hg
    J _ a hinj hrange hiso F G hF hfix hG P s hP hPs
  classical
  letI := io.toAlgebra
  have hodd : Odd (N ^ 2) := hN.pow
  obtain ⟨B, hBT, -⟩ := GlobalTheory.T.integralChart_formalBiextension_gauge_bound E H Dw l Xo c hbar T io y C
  obtain ⟨f1, -, fmul, -, -⟩ := GlobalTheory.T.formal_group_points_of_integral_chart_spec E H Dw l Xo c hbar T io y C B hBT
  have hadj := adj_mul hsim
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun h0 => hodd.pos.ne' (by rw [hkM, h0, Nat.mul_zero])
  have hprim := (GlobalTheory.T.splitKernel_formalGroup_of_rational_torsion E H Dw l Xo c hbar T io y C hC B hBT ℓ hℓ hℓu n (p * q) _ k M hk hM0
    (by rw [hadj, hkM]) hM).2
  let W : Subgroup (Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) := kerSub Xo _ (p * q) ⊓ primSub Xo _ ℓ
  have hW : ∀ u, u ∈ W ↔ ∃ i, a i = u := fun u => (hrange u).symm
  let eq : J ≃ W := Equiv.ofBijective (fun i => ⟨a i, (hW _).2 ⟨i, rfl⟩⟩)
    ⟨fun i j hij => hinj (congrArg Subtype.val hij), fun u => ((hW u).1 u.2).imp fun i hi => Subtype.ext hi⟩
  have ha : ∀ u : W, a (eq.symm u) = u := fun u => congrArg Subtype.val (eq.apply_symm_apply u)
  letI : Fintype W := Fintype.ofEquiv J eq
  have htor : ∀ (u : W) b, u.1 b ^ (N ^ 2) = 1 := fun u b => pow_eq_one_of_kills hadj u.2.1 b
  have hG' : ∀ (u : W) b, Moves Xo (u.1 b) (F b) (G (eq.symm u) b) := fun u b => by
    have := hG (eq.symm u) b
    rwa [ha] at this
  have key : ∀ (u u' : W) {F₀ F₁ F₂ F₃ : Fin n → SecN Xo (xOf y) (N ^ 2)}, (∀ b, Moves Xo (u'.1 b) (F₀ b) (F₁ b)) →
      (∀ b, Moves Xo (u.1 b) (F₁ b) (F₂ b)) → (∀ b, Moves Xo ((u * u').1 b) (F₀ b) (F₃ b)) → Rel F₃ F₂ :=
    fun u u' _ _ _ _ h₁ h₂ h₃ => rel_of_moves hodd u.1 u'.1 (htor u) (htor u')
      (fun ε hε => hiso (eq.symm u) (eq.symm u') ε (by rw [ha, ha]; exact hε)) h₁ h₂ h₃
  have hrel : ∀ {F₀ F₁ : Fin n → SecN Xo (xOf y) (N ^ 2)}, Rel F₀ F₁ →
      hv Xo c nab y.1 (N ^ 2) F₁ P = hv Xo c nab y.1 (N ^ 2) F₀ P := by
    rintro F₀ F₁ ⟨r, h1, -, h3⟩
    rw [(hv_linear E H Dw l Xo c hbar nab hnab T.Fr y.1 n P).1 (N ^ 2) F₀ F₁ (fun b => algebraMap T.V T.Fr (r b)) h3,
      ← map_prod, h1, map_one, _root_.one_mul]
  let W₀ : Subgroup W := (kerSub Xo _ q).subgroupOf W
  have hW₀ : ∀ u : W, u ∈ W₀ → ∀ x : W, Rel (G (eq.symm (x * u))) (G (eq.symm x)) := fun u hu x =>
    key x u (fun b => hfix b _ (u.2.2 b) (by
      obtain ⟨j, hj⟩ := u.2.2 b
      exact pow_eq_one_of_coprime hk₁ (pow_eq_one_of_kills hg hu b) hj)) (hG' x) (hG' (x * u))
  have hmul : ∀ u u' : ptO Xo (xOf y) ⟶ Xo.univ.t.G, (∃ α, FormPt C u α) → (∃ α, FormPt C u' α) →
      ∃ α, FormPt C (u * u') α := by
    rintro u u' ⟨α, h⟩ ⟨α', h'⟩
    obtain ⟨δ, hδ⟩ := exists_cpt (addV B.G.F (cpt α) (cpt α'))
    exact ⟨δ, fmul u u' α α' δ h h' hδ⟩
  have hpow : ∀ u : ptO Xo (xOf y) ⟶ Xo.univ.t.G, (∃ α, FormPt C u α) → ∀ m : ℕ, ∃ α, FormPt C (u ^ m) α := by
    intro u hu m
    induction m with
    | zero => exact ⟨0, by rw [pow_zero]; exact f1⟩
    | succ m ih => rw [pow_succ]; exact hmul _ _ ih hu
  let W₁ : Subgroup W :=
    { carrier := {u | ∀ b, ∃ α, FormPt C (u.1 b) α}
      one_mem' := fun b => ⟨0, f1⟩
      mul_mem' := fun {u u'} hu hu' b => hmul _ _ (hu b) (hu' b)
      inv_mem' := fun {u} hu b => by
        have h1 : u⁻¹.1 b = u.1 b ^ (N ^ 2 - 1) :=
          inv_eq_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hodd.pos]; exact htor u b)
        rw [h1]
        exact hpow _ (hu b) _ }
  obtain ⟨z, hz, hz'⟩ := sum_cosets W₀ W₁ (fun u => hv Xo c nab y.1 (N ^ 2) (G (eq.symm u)) P)
    (fun x u hu => (hrel (hW₀ u hu x)).symm) (fun z => ((-ρ : ℝ) : EReal) ≤ nval T.V e z)
    (fun I t z h => ReciprocityTheory.ChartRestriction.G.PullbackSections.le_nval_sum e t z _ h) (io s)
    (io (∏ τ : E →+* ℂ, embK c τ p.det ^ Dw.mult τ)) (fun x => by
      choose G' hG'' using fun (α : W₁) b =>
        (existsUnique_moves E H Dw l Xo T.Fr (xOf y) (N ^ 2) hodd (α.1.1 b) (htor α b) (G (eq.symm x) b)).1.exists
      have hr : ∀ α : W₁, Rel (G (eq.symm (α * x))) (G' α) := fun α => key α x (hG' x) (hG'' α) (hG' _)
      obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.sum_harmonicValues_formalKernel_similitude E H Dw l Xo c hbar T io y C hC nab hnab e ρ w n he hB ℓ hℓ hℓu N k M p q hN
        hsim hkM hk hM W₁ (fun α => α.1.1) (Subtype.val_injective.comp Subtype.val_injective)
        (fun u => ⟨by rintro ⟨α, rfl⟩; exact ⟨α.1.2.1, α.2⟩, fun ⟨h1, h2⟩ => by
          choose α hα using h2
          exact ⟨⟨⟨u, h1, hprim α ((GlobalTheory.T.kills_formalPoints_iff_mem_coordinateKernel E H Dw l Xo c hbar T io y C B hBT n _ u α hα).1 h1) u hα⟩,
            fun b => ⟨α b, hα b⟩⟩, rfl⟩⟩)
        (G (eq.symm x)) G'
        (fun b => GlobalTheory.T.reachedSection_regular_on_integralModel E H Dw l Xo c hbar T io y C hC _ _ (Reach.move _ _ _ _ (hF b) (hG' x b))) hG''
        (fun α hα => by
          have h1 := hW₀ α hα x
          rw [_root_.mul_comm] at h1
          obtain ⟨r, h2, -, h3⟩ := (h1.symm hodd.pos).trans (hr α)
          exact ⟨r, h2, h3⟩) P s hP hPs
      refine ⟨z, hz, ?_⟩
      rw [Finset.sum_congr rfl fun α _ => (hrel (hr α)).symm]
      exact hz')
  refine ⟨z, hz, ?_⟩
  have hc : Nat.card {i : J // Kills Xo q (a i)} = Nat.card W₀ := Nat.card_congr (eq.subtypeEquiv fun i => Iff.rfl)
  rw [hc, ← hz', ← eq.sum_comp]
  simp only [Equiv.symm_apply_apply]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_hv_primary_kernel_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (N k M k₁ : ℕ) (p q g : Matrix (Fin n) (Fin n) (𝓞 E)), Odd N → IsSim H (p * q) (N ^ 2) → N ^ 2 = k * M → Nat.Coprime k ℓ → AllRat Xo (xOf y) M → Nat.Coprime k₁ ℓ → g * q = ((k₁ * N : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → ∀ (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)), Function.Injective a → (∀ u : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ i, a i = u) ↔ (Kills Xo (p * q) u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1))) → (∀ i i' (ε : Fin n → Γ((ptO Xo (xOf y)).left, ⊤)ˣ), (∀ b, WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N ^ 2 : ℕ) : ℤ) (a i b) (a i' b) (ε b)) → ∏ b, ε b = 1) → ∀ (F : Fin n → SecN Xo (xOf y) (N ^ 2)) (G : J → Fin n → SecN Xo (xOf y) (N ^ 2)), (∀ b, Reach Xo (sOf1 y) (N ^ 2) (F b)) → (∀ b (u : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)), (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u (F b) (F b)) → (∀ i b, Moves Xo (a i b) (F b) (G i b)) → ∀ (P : MvPolynomial (LtN Dw n) c.F) (s : c.F), P ∈ HH c w n → MvPolynomial.map io (MvPolynomial.C s * pushL c ((p * q).map (algebraMap (𝓞 E) E)) P) ∈ FFV (Dw := Dw) T w n → letI := io.toAlgebra; ∃ z : T.Fr, ((-ρ : ℝ) : EReal) ≤ nval T.V e z ∧ io s * ∑ i, hv Xo c nab y.1 (N ^ 2) (G i) P = (Nat.card {i : J // Kills Xo q (a i)} : T.Fr) * io (∏ τ : E →+* ℂ, embK c τ p.det ^ Dw.mult τ) * z := by
  atlas_forward_decl GlobalTheory.sum_hv_primary_kernel
end

section
section
set_option autoImplicit false

namespace GlobalTheory.TorsCount

theorem card_primary (C : Type) [AddCommGroup C] [Finite C] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    Nat.card {c : C // ∃ j : ℕ, ℓ ^ j • c = 0} = ℓ ^ (Nat.card C).factorization ℓ := by
  haveI := Fact.mk hℓ
  let P : Sylow ℓ (Multiplicative C) :=
    ⟨CommGroup.primaryComponent (Multiplicative C) ℓ, CommGroup.primaryComponent.isPGroup, fun {Q} hQ hle =>
      le_antisymm (fun x hx => by
        obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
        exact CommGroup.mem_primaryComponent.2 ⟨k, congrArg Subtype.val hk⟩) hle⟩
  have h := Sylow.card_eq_multiplicity P
  rw [Nat.card_congr (Multiplicative.toAdd (α := C))] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun c =>
    (CommGroup.mem_primaryComponent (G := Multiplicative C) (g := Multiplicative.ofAdd c)).symm)

theorem exists_inv {k m : ℕ} (h : Nat.Coprime k m) : ∃ a : ℤ, ∀ (U : Type) [AddCommGroup U] (u : U), m • u = 0 →
    a • k • u = u := by
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h)
  refine ⟨a, fun U _ u hu => ?_⟩
  have : (a * k + b * m) • u = u := by rw [hab, one_smul]
  rwa [add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hu, smul_zero, add_zero] at this

theorem card_ker_eq {W U : Type} [AddCommGroup W] [AddCommGroup U] (Q G : W →ₗ[ℤ] W) (Q' : U →+ U) (ev : W →+ U)
    (k M ℓ : ℕ) (hk : Nat.Coprime k ℓ) (hk0 : k ≠ 0) (hM : M ≠ 0) (tf : ∀ (m : ℕ) (w : W), m ≠ 0 → m • w = 0 → w = 0)
    (hev : ∀ w, Q' (ev w) = ev (Q w)) (hGQ : ∀ w, G (Q w) = (k * M) • w) (hQG : ∀ w, Q (G w) = (k * M) • w)
    (hker : ∀ w, ev w = 0 ↔ ∃ b, w = M • b) (honto : ∀ u, M • u = 0 → ∃ w, ev w = u)
    (hQ' : ∀ u, Q' u = 0 → (k * M) • u = 0) :
    Nat.card {u : U // Q' u = 0 ∧ ∃ j : ℕ, ℓ ^ j • u = 0} =
      Nat.card {c : W ⧸ LinearMap.range Q // ∃ j : ℕ, ℓ ^ j • c = 0} := by
  have hM0 : ∀ w, ev (M • w) = 0 := fun w => (hker _).2 ⟨w, rfl⟩
  let φ : (W ⧸ LinearMap.range Q) →ₗ[ℤ] U := (LinearMap.range Q).liftQ (ev.toIntLinearMap ∘ₗ G) (by
    rintro _ ⟨w, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, AddMonoidHom.coe_toIntLinearMap]
    rw [hGQ, mul_comm, mul_smul, hM0])
  have hφ : ∀ w, φ (Submodule.Quotient.mk w) = ev (G w) := fun w => rfl
  have hφk : ∀ c, φ c = 0 → k • c = 0 := fun c hc => by
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨b, hb⟩ := (hker _).1 ((hφ w).symm.trans hc)
    have h1 : M • (k • w - Q b) = 0 := by
      rw [smul_sub, smul_smul, mul_comm, ← hQG, hb, map_nsmul, sub_self]
    have h2 := sub_eq_zero.1 (tf M _ hM h1)
    change (LinearMap.range Q).mkQ (k • w) = 0
    rw [h2]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩
  symm
  refine Nat.card_eq_of_bijective (fun c => ⟨φ c.1, ?_, ?_⟩) ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ c.1
    rw [← hw, hφ, hev, hQG, mul_comm, mul_smul, hM0]
  · obtain ⟨j, hj⟩ := c.2
    exact ⟨j, by rw [← map_nsmul, hj, map_zero]⟩
  · rintro ⟨c, i, hi⟩ ⟨d, j, hj⟩ h
    have h1 : φ (c - d) = 0 := by rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val h)
    obtain ⟨a, ha⟩ := exists_inv (hk.pow_right (i + j))
    have h2 := ha _ (c - d) (by
      rw [smul_sub, pow_add, mul_smul _ _ d, hj, mul_comm, mul_smul, hi, smul_zero, smul_zero, sub_zero])
    rw [hφk _ h1, smul_zero] at h2
    exact Subtype.ext (sub_eq_zero.1 h2.symm)
  · rintro ⟨u, hu, j, hj⟩
    obtain ⟨a, ha⟩ := exists_inv (hk.pow_right j)
    have h1 : M • u = 0 := by
      rw [← ha _ (M • u) (by rw [smul_comm, hj, smul_zero]), smul_smul k, hQ' u hu, smul_zero]
    obtain ⟨v, rfl⟩ := honto u h1
    obtain ⟨w, hw⟩ := (hker _).1 ((hev v).symm.trans hu)
    have h2 : M • (G w - k • v) = 0 := by
      rw [smul_sub, smul_smul, mul_comm, ← hGQ, hw, map_nsmul, sub_self]
    have h3 : φ (Submodule.Quotient.mk w) = k • ev v := by
      rw [hφ, sub_eq_zero.1 (tf M _ hM h2), map_nsmul]
    refine ⟨⟨a • k • a • Submodule.Quotient.mk w, j, ?_⟩, Subtype.ext ?_⟩
    · have h4 := hφk (ℓ ^ j • Submodule.Quotient.mk w) (by rw [map_nsmul, h3, smul_comm, hj, smul_zero])
      rw [smul_comm k a, smul_comm _ a, smul_comm _ a, smul_comm, smul_comm (ℓ ^ j) k, h4, smul_zero, smul_zero]
    · change φ _ = ev v
      rw [map_zsmul, map_nsmul, map_zsmul, h3, ha _ _ hj, ha _ _ hj]

theorem det_eq_of_intertwine {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module.Free ℤ A] [Module.Finite ℤ A]
    [Module.Free ℤ B] [Module.Finite ℤ B] (h : Module.finrank ℤ A = Module.finrank ℤ B) (f : A →ₗ[ℤ] A) (g : B →ₗ[ℤ] B)
    (i : A →ₗ[ℤ] B) (hi : Function.Injective i) (hc : g ∘ₗ i = i ∘ₗ f) : LinearMap.det g = LinearMap.det f := by
  let e : A ≃ₗ[ℤ] B := LinearEquiv.ofFinrankEq A B h
  have h0 : LinearMap.det (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ≠ 0 := by
    intro h0
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    exact h0 (LinearMap.ker_eq_bot.2 (hi.comp e.symm.injective))
  have h1 : g ∘ₗ (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) =
      (i ∘ₗ (e.symm : B →ₗ[ℤ] A)) ∘ₗ ((e : A →ₗ[ℤ] B) ∘ₗ f ∘ₗ (e.symm : B →ₗ[ℤ] A)) := by
    ext x
    simpa using LinearMap.congr_fun hc (e.symm x)
  have h2 := congrArg LinearMap.det h1
  rw [LinearMap.det_comp, LinearMap.det_comp (i ∘ₗ _), LinearMap.det_conj, mul_comm] at h2
  exact mul_left_cancel₀ h0 h2

section Mat
variable {O : Type} [CommRing O] {n : ℕ}

def mact (L : Type) [AddCommGroup L] [Module O L] (mu : Matrix (Fin n) (Fin n) O) : (Fin n → L) →ₗ[O] (Fin n → L) where
  toFun u i := ∑ j, mu i j • u j
  map_add' u v := by ext i; simp [Finset.sum_add_distrib]
  map_smul' a u := by ext i; simp [Finset.smul_sum, smul_comm a]

variable {L : Type} [AddCommGroup L] [Module O L]

theorem mact_apply (mu : Matrix (Fin n) (Fin n) O) (u : Fin n → L) (i : Fin n) : mact L mu u i = ∑ j, mu i j • u j := rfl

theorem mact_mul (a b : Matrix (Fin n) (Fin n) O) (u : Fin n → L) : mact L a (mact L b u) = mact L (a * b) u := by
  ext i
  simp only [mact_apply, Matrix.mul_apply, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

theorem mact_nat (c : ℕ) (u : Fin n → L) : mact L ((c : O) • (1 : Matrix (Fin n) (Fin n) O)) u = c • u := by
  ext i
  simp only [mact_apply, Matrix.smul_apply, Matrix.one_apply, smul_ite, smul_zero, ite_smul, smul_one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Nat.cast_smul_eq_nsmul, smul_assoc, one_smul, Pi.smul_apply]

theorem det_mact [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O] [Module.Finite O L]
    [Module.Free ℤ L] (q : Matrix (Fin n) (Fin n) O) :
    LinearMap.det ((mact L q).restrictScalars ℤ) = Algebra.norm ℤ q.det ^ Module.finrank O L := by
  have : Module.Finite ℤ L := Module.Finite.trans O L
  obtain ⟨r, hr⟩ : ∃ r, r = Module.finrank O L := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := L) hr.le
  rw [← hr]
  let f : (Fin r → Fin n → O) →ₗ[O] (Fin r → Fin n → O) :=
    LinearMap.pi fun s => (Matrix.toLin' q).comp (LinearMap.proj s)
  have hf : LinearMap.det f = q.det ^ r := by
    simp [f, LinearMap.det_pi]
  let i : (Fin r → Fin n → O) →ₗ[O] (Fin n → L) :=
    { toFun c j := ∑ s, c s j • v s
      map_add' c d := by ext j; simp [add_smul, Finset.sum_add_distrib]
      map_smul' a c := by ext j; simp [Finset.smul_sum, mul_smul] }
  have hi : Function.Injective i := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    ext s j
    have h1 : ∑ s, c s j • v s = 0 := congrFun hc j
    exact Fintype.linearIndependent_iff.1 hv (fun s => c s j) h1 s
  rw [det_eq_of_intertwine ?_ (f.restrictScalars ℤ) _ (i.restrictScalars ℤ) hi ?_, LinearMap.det_restrictScalars, hf,
    map_pow]
  · simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [finrank_int_eq_mul_of_finite (O := O) (M := L), ← hr]; ring
  · refine LinearMap.ext fun c => funext fun j => ?_
    change ∑ b, q j b • ∑ s, c s b • v s = ∑ s, (q.mulVec (c s) j) • v s
    simp only [Finset.smul_sum, Matrix.mulVec, dotProduct, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm

theorem card_kills [IsDomain O] [CharZero O] [Module.Free ℤ O] [Module.Finite ℤ O] [Module.Finite O L]
    [Module.Free ℤ L] {P : Type} [AddCommGroup P] [Module O P] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (q g : Matrix (Fin n) (Fin n) O) (k M : ℕ) (hk : Nat.Coprime k ℓ) (hM : 0 < M)
    (hgq : g * q = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) (ev : L →ₗ[O] P)
    (hker : ∀ a, ev a = 0 ↔ ∃ b, a = M • b) (honto : ∀ w : P, M • w = 0 → ∃ a, ev a = w) :
    Nat.card {u : Fin n → P // mact P q u = 0 ∧ ∃ j : ℕ, ℓ ^ j • u = 0} =
      ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L).factorization ℓ := by
  have : Module.Finite ℤ L := Module.Finite.trans O L
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hℓ.one_lt.ne' (by simpa using hk)
  have hc : k * M ≠ 0 := mul_ne_zero hk0 hM.ne'
  have tf : ∀ (m : ℕ) (w : Fin n → L), m ≠ 0 → m • w = 0 → w = 0 := fun m w hm h => by
    rw [← natCast_zsmul] at h
    exact (smul_eq_zero.1 h).resolve_left (by exact_mod_cast hm)
  have hGQ : ∀ w, mact L g (mact L q w) = (k * M) • w := fun w => by rw [mact_mul, hgq, mact_nat]
  have hdet : q.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hgq
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hc) h1.symm
  have hqg : q * g = ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O) := by
    have h1 : (q * g - ((k * M : ℕ) : O) • (1 : Matrix (Fin n) (Fin n) O)) * q = 0 := by
      rw [sub_mul, Matrix.mul_assoc, hgq]; simp
    have h2 := congrArg (· * q.adjugate) h1
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul] at h2
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hdet)
  have hQG : ∀ w, mact L q (mact L g w) = (k * M) • w := fun w => by rw [mact_mul, hqg, mact_nat]
  have hinj : Function.Injective ((mact L q).restrictScalars ℤ) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    refine tf _ w hc ?_
    rw [← hGQ, show mact L q w = 0 from hw, map_zero]
  have hcard : Nat.card ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) =
      (Algebra.norm ℤ q.det).natAbs ^ Module.finrank O L := by
    rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj), ← Int.natAbs_pow, ← det_mact (L := L) q]
    congr 2
  have hfin : Finite ((Fin n → L) ⧸ LinearMap.range ((mact L q).restrictScalars ℤ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ (Int.natAbs_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hdet))
  rw [← hcard, ← card_primary _ ℓ hℓ]
  refine card_ker_eq ((mact L q).restrictScalars ℤ) ((mact L g).restrictScalars ℤ) (mact P q).toAddMonoidHom
    (ev.compLeft (Fin n)).toAddMonoidHom k M ℓ hk hk0 hM.ne' tf (fun w => ?_) hGQ hQG (fun w => ?_) (fun u hu => ?_)
    (fun u hu => ?_)
  · ext i
    simp [mact_apply]
  · constructor
    · intro h
      choose b hb using fun i => (hker (w i)).1 (congrFun h i)
      exact ⟨b, funext hb⟩
    · rintro ⟨b, rfl⟩
      exact funext fun i => (hker _).2 ⟨b i, rfl⟩
  · choose a ha using fun i => honto (u i) (congrFun hu i)
    exact ⟨a, funext ha⟩
  · rw [← mact_nat (O := O), ← hgq, ← mact_mul, show mact P q u = 0 from hu, map_zero]
end Mat

end GlobalTheory.TorsCount

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory

theorem card_kills_primary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (ℓ : ℕ), ℓ.Prime → ∀ (n : ℕ) (q g : Matrix (Fin n) (Fin n) (𝓞 E)) (k M : ℕ), Nat.Coprime k ℓ → 0 < M → g * q = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → AllRat Xo x M → Nat.card {u : Fin n → (ptO Xo x ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)} = ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ (Dw.p + Dw.q)).factorization ℓ := by
  intro E _ _ _ H Dw l Xo K _ x ℓ hℓ n q g k M hk hM hgq hall
  obtain ⟨ev, hadd, hlin, hker, honto⟩ := ((GlobalTheory.T.torsion_rational_over_finite_extension_level_structure E H Dw l Xo K x M hM).2 hall).2
  letI := ZPart.ptMod Xo (ptO Xo x)
  have := Dw.fin
  have := datum_free_int Dw
  let ev' : Dw.La →ₗ[𝓞 E] Additive (ptO Xo x ⟶ Xo.univ.t.G) :=
    { toFun a := Additive.ofMul (ev a)
      map_add' a b := congrArg Additive.ofMul (hadd a b)
      map_smul' o a := congrArg Additive.ofMul (hlin o a) }
  rw [← Dw.rank, ← TorsCount.card_kills ℓ hℓ q g k M hk hM hgq ev' (fun a => hker a) (fun w hw => honto w.toMul hw)]
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.piCongrRight fun _ => Additive.ofMul) fun u => ?_)
  refine and_congr ((ZPart.kills_iff Xo q u).trans funext_iff.symm) ⟨fun h => ?_, fun ⟨j, hj⟩ b => ⟨j, congrFun hj b⟩⟩
  choose e he using h
  refine ⟨∑ b, e b, funext fun b => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
    (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
  change u b ^ (ℓ ^ ∑ b, e b) = 1
  rw [hd, pow_add, pow_mul, he, one_pow]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_primaryTorsionTuples_killed_by_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X) (ℓ : ℕ), ℓ.Prime → ∀ (n : ℕ) (q g : Matrix (Fin n) (Fin n) (𝓞 E)) (k M : ℕ), Nat.Coprime k ℓ → 0 < M → g * q = ((k * M : ℕ) : 𝓞 E) • (1 : Matrix (Fin n) (Fin n) (𝓞 E)) → AllRat Xo x M → Nat.card {u : Fin n → (ptO Xo x ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, (∃ j : ℕ, u b ^ (ℓ ^ j) = 1)} = ℓ ^ ((Algebra.norm ℤ q.det).natAbs ^ (Dw.p + Dw.q)).factorization ℓ := by
  atlas_forward_decl GlobalTheory.card_kills_primary
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (m m' : ℕ), a ^ k = 1 → b ^ k = 1 → Nat.Coprime m m' → a ^ m = 1 → b ^ m' = 1 → ∀ F F₁ F₂ : SecN Xo x k, Moves Xo b F F₁ → (Moves Xo a F₁ F₂ ↔ Moves Xo (a * b) F F₂) := by
  first | exact @GlobalTheory.PlaceInt.moves_mul_of_coprime | exact GlobalTheory.PlaceInt.moves_mul_of_coprime | (intros; apply GlobalTheory.PlaceInt.moves_mul_of_coprime <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

set_option autoImplicit false

namespace GlobalTheory.ShortPrime

section Val
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

def Un (V : Type) {K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (x : K) : Prop := valV V x = 1

theorem Un.mul {x y : K} (hx : Un V x) (hy : Un V y) : Un V (x * y) := by
  unfold Un at *; rw [map_mul, hx, hy, _root_.one_mul]

theorem Un.inv {x : K} (hx : Un V x) : Un V x⁻¹ := by
  unfold Un at *; rw [map_inv₀, hx, inv_one]

theorem Un.pow {x : K} (hx : Un V x) (n : ℕ) : Un V (x ^ n) := by
  unfold Un at *; rw [map_pow, hx, one_pow]

theorem Un.ne {x : K} (hx : Un V x) : x ≠ 0 := by
  rintro rfl; simp [Un] at hx

theorem Un.nval {x : K} (hx : Un V x) (e : ℕ) (z : K) : nval V e (x * z) = nval V e z :=
  nval_mul_unit e hx.ne (by unfold Un at hx; simp [vV, hx]) z

theorem un_of_vV {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (h : vV V x = vV V y) : Un V (x * y⁻¹) := by
  unfold Un
  have h1 : WithZero.log (valV V x) = WithZero.log (valV V y) := neg_injective h
  have h2 : valV V x = valV V y := by
    rw [← WithZero.exp_log (valV_ne_zero (V := V) hx), h1, WithZero.exp_log (valV_ne_zero (V := V) hy)]
  rw [map_mul, map_inv₀, h2, mul_inv_cancel₀ (valV_ne_zero hy)]

theorem isUnit_of_coprime {ℓ k : ℕ} (hl : ¬ IsUnit (ℓ : V)) (h : Nat.Coprime k ℓ) : IsUnit (k : V) := by
  obtain ⟨a, b, hab⟩ : IsCoprime (k : V) (ℓ : V) := h.cast
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h1 | h1
  · exact isUnit_of_mul_isUnit_right h1
  · exact absurd (isUnit_of_mul_isUnit_right h1) hl

theorem un_of_coprime {ℓ k : ℕ} (hl : ¬ IsUnit (ℓ : V)) (h : Nat.Coprime k ℓ) : Un V (k : K) := by
  unfold Un valV
  rw [← map_natCast (algebraMap V K), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm (isUnit_of_coprime hl h)

theorem un_ordProj [CharZero K] {ℓ m : ℕ} (hp : ℓ.Prime) (hl : ¬ IsUnit (ℓ : V)) (hm : m ≠ 0) :
    Un V (((ℓ ^ m.factorization ℓ : ℕ) : K) * (m : K)⁻¹) := by
  have h := (un_of_coprime (K := K) hl (Nat.coprime_ordCompl hp hm).symm).inv
  convert h using 1
  have h1 : (m : K) = ((ℓ ^ m.factorization ℓ : ℕ) : K) * ((m / ℓ ^ m.factorization ℓ : ℕ) : K) := by
    rw [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have h2 : ((ℓ ^ m.factorization ℓ : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hp.ne_zero)
  generalize ((m / ℓ ^ m.factorization ℓ : ℕ) : K) = t at *
  rw [h1, mul_inv, ← _root_.mul_assoc, mul_inv_cancel₀ h2, _root_.one_mul]

theorem le_nval_sum {J : Type} (s : Finset J) (e : ℕ) (r : EReal) (f : J → K) (h : ∀ i ∈ s, r ≤ nval V e (f i)) :
    r ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, nval_zero]; exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (le_min (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).trans
      (nval_add e _ _)
end Val

theorem eq_one_of_coprime {G : Type} [Monoid G] {u : G} {k ℓ : ℕ} (h : Nat.Coprime k ℓ) (h1 : u ^ k = 1)
    (h2 : ∃ j : ℕ, u ^ (ℓ ^ j) = 1) : u = 1 := by
  obtain ⟨j, hj⟩ := h2
  rw [← orderOf_eq_one_iff]
  exact Nat.eq_one_of_dvd_coprimes (h.pow_right j) (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hj)

section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l)

theorem comp_act_nat {T : Over Xo.X} (u : T ⟶ Xo.univ.t.G) (k : ℕ) : u ≫ Xo.univ.t.act.act (k : 𝓞 E) = u ^ k := by
  rw [ZhStable.act_natCast, MonObj.comp_pow, Category.comp_id]

theorem kills_pow {T : Over Xo.X} {n : ℕ} {mu : Matrix (Fin n) (Fin n) (𝓞 E)} {u : Fin n → (T ⟶ Xo.univ.t.G)}
    (h : Kills Xo mu u) (k : ℕ) : Kills Xo mu (fun b => u b ^ k) := by
  letI := ZPart.ptMod Xo T
  rw [ZPart.kills_iff] at h ⊢
  intro i
  simp only [ofMul_pow, smul_comm (mu i _) k]
  rw [← Finset.smul_sum, h i, smul_zero]

theorem kills_mul {T : Over Xo.X} {n : ℕ} {mu : Matrix (Fin n) (Fin n) (𝓞 E)} {u : Fin n → (T ⟶ Xo.univ.t.G)}
    (h : Kills Xo mu u) (nu : Matrix (Fin n) (Fin n) (𝓞 E)) : Kills Xo (nu * mu) u := by
  letI := ZPart.ptMod Xo T
  rw [ZPart.kills_iff] at h ⊢
  exact h.mul nu

theorem nat_mul_bar (k : ℕ) : (k : 𝓞 E) * H.bar (k : 𝓞 E) = ((k ^ 2 : ℕ) : 𝓞 E) := by
  rw [map_natCast]; push_cast; ring

variable {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}

theorem moves_comm {k : ℕ} (hk : Odd k) {u t : ptO Xo x ⟶ Xo.univ.t.G} {m ℓ : ℕ} (hu : u ^ k = 1) (ht : t ^ k = 1)
    (hc : Nat.Coprime m ℓ) (hul : ∃ j : ℕ, u ^ (ℓ ^ j) = 1) (htm : t ^ m = 1) {A A' B B' : SecN Xo x k}
    (h1 : Moves Xo u A A') (h2 : Moves Xo t A B) (h3 : Moves Xo t A' B') : Moves Xo u B B' := by
  obtain ⟨j, hj⟩ := hul
  have h4 := (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x k hk t u m (ℓ ^ j) ht hu (hc.pow_right j) htm hj A A' B' h1).1 h3
  rw [_root_.mul_comm] at h4
  exact (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x k hk u t (ℓ ^ j) m hu ht (hc.pow_right j).symm hj htm A B B' h2).2 h4
end Pts

section Base
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}

theorem exists_base {N ℓ m m' : ℕ} (hN : Odd N) (s : SecN Xo x 1) (a' t : ptO Xo x ⟶ Xo.univ.t.G)
    (ha' : a' ^ (N ^ 2) = 1) (ht : t ^ (N ^ 2) = 1) (hm : Nat.Coprime m ℓ) (hm' : Nat.Coprime m' ℓ)
    (ham : a' ^ m = 1) (htm : t ^ m' = 1) :
    ∃ F₀ : SecN Xo x (N ^ 2), Reach Xo s (N ^ 2) F₀ ∧
      (∀ u : ptO Xo x ⟶ Xo.univ.t.G, (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u F₀ F₀) ∧
      ∀ (a : ptO Xo x ⟶ Xo.univ.t.G) F, (∃ j : ℕ, a ^ (ℓ ^ j) = 1) → a ^ (N ^ 2) = 1 →
        IsUUOver Xo.univ.t.G Xo.univ.t.PP N s (a * a') t F → Moves Xo a F₀ (sqN Xo N F) := by
  have hN2 : Odd (N ^ 2) := hN.pow
  obtain ⟨G₀, hG₀, hG₀u⟩ := GlobalTheory.existsUnique_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) (nat_mul_bar N)
    (Nat.one_mul _).symm s
  obtain ⟨F₁, hF₁, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 a' ha' G₀).1
  obtain ⟨F₀, hF₀, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x (N ^ 2) hN2 t ht F₁).1
  refine ⟨F₀, ?_, fun u hu huN => ?_, fun a F ha haN hF => ?_⟩
  · exact .move _ _ _ _ (.move _ _ _ _ (.pull 1 (N ^ 2) (N ^ 2) (N : 𝓞 E) s G₀ .base (Or.inl rfl) hN2
      (nat_mul_bar N) (Nat.one_mul _).symm hG₀) hF₁) hF₀
  · have hu2 : u ^ (N ^ 2) = 1 := by rw [pow_two, pow_mul, huN, one_pow]
    have h0 : Moves Xo u G₀ G₀ := moves_of_pulls E H Dw l Xo S x (N : 𝓞 E) (N ^ 2) 1 (N ^ 2) (nat_mul_bar N)
      (Nat.one_mul _).symm hN2 1 u ((comp_act_nat Xo u N).trans huN) hu2 s s G₀ G₀
      (GlobalTheory.existsUnique_moves E H Dw l Xo S x 1 odd_one 1 (one_pow _) s).2 hG₀ hG₀
    exact moves_comm Xo hN2 hu2 ht hm' hu htm (moves_comm Xo hN2 hu2 ha' hm hu ham h0 hF₁ hF₁) hF₀ hF₀
  · obtain ⟨G, F₂, hG, h2, h3⟩ := ((uu_through_moves E H Dw l Xo S x N hN s).1 (a * a') t F
      (by rw [mul_pow, haN, ha', _root_.one_mul]) ht).1 hF
    obtain rfl := hG₀u G hG
    obtain ⟨j, hj⟩ := ha
    have h4 := (GlobalTheory.T.symmetricTranslate_mul_of_coprime_orders E H Dw l Xo S x _ hN2 a a' (ℓ ^ j) m haN ha' (hm.pow_right j).symm hj ham
      G F₁ F₂ hF₁).2 h2
    exact moves_comm Xo hN2 haN ht hm' ⟨j, hj⟩ htm h4 hF₀ h3

theorem exists_perm {T : Over Xo.X} {n k ℓ : ℕ} (hk : Nat.Coprime k ℓ) (mu : Matrix (Fin n) (Fin n) (𝓞 E))
    {J : Type} [Fintype J] (a : J → Fin n → (T ⟶ Xo.univ.t.G)) (hinj : Function.Injective a)
    (ha : ∀ u, (∃ i, a i = u) ↔ (Kills Xo mu u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) :
    ∃ π : J ≃ J, ∀ i b, a (π i) b = a i b ^ k := by
  have h1 : ∀ i, ∃ i', a i' = fun b => a i b ^ k := fun i => by
    obtain ⟨h1, h2⟩ := (ha _).1 ⟨i, rfl⟩
    exact (ha _).2 ⟨kills_pow Xo h1 k, fun b => (h2 b).imp fun j hj => by rw [pow_right_comm, hj, one_pow]⟩
  choose π hπ using h1
  have h2 : Function.Injective π := fun i i' h => hinj <| funext fun b => by
    have h3 : a i b ^ k = a i' b ^ k := by
      have := hπ i
      rw [h, hπ i'] at this
      exact (congrFun this b).symm
    obtain ⟨j, hj⟩ := ((ha _).1 ⟨i, rfl⟩).2 b
    obtain ⟨j', hj'⟩ := ((ha _).1 ⟨i', rfl⟩).2 b
    refine div_eq_one.1 (eq_one_of_coprime hk (by rw [div_pow, h3, div_self']) ⟨j + j', ?_⟩)
    rw [div_pow, pow_add, pow_mul, hj, one_pow, _root_.mul_comm, pow_mul, hj', one_pow, div_self']
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.1 h2), fun i b => congrFun (hπ i) b⟩

theorem card_kills {T : Over Xo.X} {n ℓ : ℕ} (p q : Matrix (Fin n) (Fin n) (𝓞 E))
    {J : Type} (a : J → Fin n → (T ⟶ Xo.univ.t.G)) (hinj : Function.Injective a)
    (ha : ∀ u, (∃ i, a i = u) ↔ (Kills Xo (p * q) u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1)) :
    Nat.card {i : J // Kills Xo q (a i)} =
      Nat.card {u : Fin n → (T ⟶ Xo.univ.t.G) // Kills Xo q u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1} := by
  refine Nat.card_eq_of_bijective (fun i => ⟨a i.1, i.2, ((ha _).1 ⟨i.1, rfl⟩).2⟩) ⟨fun i i' h => ?_, fun u => ?_⟩
  · exact Subtype.ext (hinj (congrArg Subtype.val h))
  · obtain ⟨i, hi⟩ := (ha u.1).2 ⟨kills_mul Xo u.2.1 p, u.2.2⟩
    exact ⟨⟨i, hi ▸ u.2.1⟩, Subtype.ext hi⟩
end Base

section Core
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem one_or_four_le {N : ℕ} (hN : Odd N) : N ^ 2 = 1 ∨ 4 ≤ N ^ 2 := by
  obtain ⟨r, rfl⟩ := hN
  rcases r with _ | r
  · exact Or.inl rfl
  · exact Or.inr (le_trans (by norm_num : 4 ≤ 3 ^ 2) (Nat.pow_le_pow_left (by omega) 2))

theorem un_nrm (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) {k ℓ : ℕ} (hl : ¬ IsUnit (ℓ : T.V)) (hk : Nat.Coprime k ℓ)
    (w : (E →+* ℂ) × ℕ → ℕ) : Un T.V (io (nrm Dw c w (k : 𝓞 E))) := by
  simp only [nrm, map_natCast, Finset.prod_pow_eq_pow_sum, map_pow]
  exact (un_of_coprime hl hk).pow _

theorem ell_part (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a) (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C) (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e) (hB : ChBound C e ρ w n)
    (ℓ : ℕ) (hp : ℓ.Prime) (hl : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N M : ℕ) (hU : Λ.Unimod) (hL : Λ.LevOK N M)
    (β : c.F) (hβ0 : β ≠ 0) (hβ : BetaIs (Dw := Dw) c Λ β) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (hR : AllRat Xo (xOf y) (N ^ 2)) (J : Type) [Fintype J] (a : J → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (hinj : Function.Injective a) (ha : ∀ u, (∃ i, a i = u) ↔ (InZh Xo Λ N u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1))
    (F₀ : Fin n → SecN Xo (xOf y) (N ^ 2)) (F : J → Fin n → SecN Xo (xOf y) (N ^ 2))
    (hre : ∀ b, Reach Xo (sOf1 y) (N ^ 2) (F₀ b))
    (hfix : ∀ b (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G), (∃ j : ℕ, u ^ (ℓ ^ j) = 1) → u ^ N = 1 → Moves Xo u (F₀ b) (F₀ b))
    (hF : ∀ i b, Moves Xo (a i b) (F₀ b) (F i b)) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
      ∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) := by
  letI := io.toAlgebra
  obtain ⟨A, hsim⟩ := GlobalTheory.T.exists_adapted_similitude_data_at_prime E H n Λ N M ℓ hU hL hp
  have hN : Odd N := hL.1
  have hkN : Odd (A.k * N) := A.odd.mul hN
  have hlev : (A.k * N) ^ 2 = N ^ 2 * A.k ^ 2 := by ring
  have hz := fun u hu => GlobalTheory.inZh_iff_kills_adapted E H Dw l Xo n Λ N ℓ hp hN.pos A (ptO Xo (xOf y)) u hu
  have ha' : ∀ u, (∃ i, a i = u) ↔ (Kills Xo (A.p * A.q) u ∧ ∀ b, ∃ j : ℕ, u b ^ (ℓ ^ j) = 1) := fun u =>
    (ha u).trans (and_congr_left fun hu => (hz u hu).1)
  have hZ : ∀ i, InZh Xo Λ (A.k * N) (a i) := fun i =>
    have h := (ha' _).1 ⟨i, rfl⟩
    (hz _ h.2).2.2 h.1
  obtain ⟨π, hπ⟩ := exists_perm Xo A.cop _ a hinj ha'
  have hpull := fun G => (GlobalTheory.existsUnique_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2)
    (nat_mul_bar A.k) hlev G).exists
  choose pl hpl using hpull
  have hmv : ∀ (u : ptO Xo (xOf y) ⟶ Xo.univ.t.G) G G', u ^ ((A.k * N) ^ 2) = 1 → Moves Xo (u ^ A.k) G G' →
      Moves Xo u (pl G) (pl G') := fun u G G' hu h =>
    moves_of_pulls E H Dw l Xo _ (xOf y) (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) ((A.k * N) ^ 2) (nat_mul_bar A.k) hlev
      hkN.pow _ u (comp_act_nat Xo u A.k) hu G G' _ _ h (hpl G) (hpl G')
  have hsub : Ideal.span {((A.k * N : ℕ) : 𝓞 E)} • stdLat E n ≤ Λ.La := by
    refine le_trans (Submodule.smul_mono_left ?_) (hL.2.2.trans inf_le_left)
    rw [Nat.cast_mul]
    exact Ideal.span_singleton_le_span_singleton.2 (dvd_mul_left _ _)
  have hiso := (GlobalTheory.zh_isotropic_and_half_isotropic GlobalTheory.firstFiveLaws.1 E H Dw l Xo _ (xOf y) n Λ (A.k * N) hU
    hkN.pos hsub).1
  obtain ⟨hff, -, hhom⟩ := GlobalTheory.PushIntegral.map_pushL_mem_FFV E H Dw l c n Λ w P hP T io A.k A.ga
    (isUnit_of_coprime hl A.cop) A.unitary A.into
  have hkN0 : ((A.k * N : ℕ) : c.F) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hkN.pos.ne')
  obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.sum_hv_primary_kernel_alt E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl (A.k * N)
    (A.k ^ 2) (N ^ 2) A.k₁ A.p A.q ((A.k : 𝓞 E) • A.g) hkN hsim (mul_pow _ _ _) (A.cop.pow_left 2) hR A.cop₁
    (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) J a hinj ha'
    (fun i i' ε hε => hiso (a i) (a i') ε (hZ i) (hZ i') fun b => by rw [← Nat.cast_pow]; exact hε b)
    (fun b => pl (F₀ b)) (fun i b => pl (F (π i) b))
    (fun b => .pull (N ^ 2) (A.k ^ 2) _ (A.k : 𝓞 E) (F₀ b) _ (hre b)
      (one_or_four_le hN)
      A.odd.pow (nat_mul_bar A.k) hlev (hpl _))
    (fun b u hu huN => hmv u _ _ (by rw [pow_two, pow_mul, huN, one_pow]) (hfix b _
      (hu.imp fun j hj => by rw [pow_right_comm, hj, one_pow]) (by rw [← pow_mul, huN])))
    (fun i b => hmv _ _ _ ((hZ i).1 b) (by rw [← hπ]; exact hF _ _))
    P (((A.k * N : ℕ) : c.F) ^ P.totalDegree)⁻¹ hP.1
    (by rw [A.prod, hhom, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hkN0, map_one, _root_.one_mul]; exact hff)
  have hch : ∀ i, hv Xo c nab y.1 ((A.k * N) ^ 2) (fun b => pl (F (π i) b)) P =
      io (nrm Dw c w (A.k : 𝓞 E)) * hv Xo c nab y.1 (N ^ 2) (F (π i)) P := fun i =>
    GlobalTheory.T.harmonic_value_chain_rule_normalized_pullback E H Dw l Xo c hst nab hnab T.Fr y.1 (A.k : 𝓞 E) (A.k ^ 2) (N ^ 2) _ (nat_mul_bar A.k) hlev n
      (F (π i)) _ (fun b => hpl _) w P hP.1
  obtain ⟨hi1, hi2, hi3⟩ := GlobalTheory.LatticeIndex.latidx E H Dw l c n Λ N M ℓ hU hL hp A
  obtain ⟨hi4, hi5⟩ := hi3 β hβ0 hβ T io hl
  have hcnt := GlobalTheory.T.card_primaryTorsionTuples_killed_by_matrix E H Dw l Xo T.Fr (xOf y) ℓ hp n A.q ((N : 𝓞 E) • A.g) A.k₁ (N ^ 2) A.cop₁
    (pow_pos hN.pos 2) (by rw [Matrix.smul_mul, A.gq, smul_smul]; congr 1; push_cast; ring) hR
  rw [card_kills Xo A.p A.q a hinj ha', hcnt, hi1, Finset.sum_congr rfl fun i _ => hch i, ← Finset.mul_sum,
    Equiv.sum_comp π fun i => hv Xo c nab y.1 (N ^ 2) (F i) P] at hz2
  have hδ : io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ) ≠ 0 := by
    refine (map_ne_zero io).2 (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_)
    exact (map_ne_zero (embF c τ)).2 ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hi5)
  have u1 := un_of_vV hδ ((map_ne_zero io).2 hβ0) hi4
  have u2 := un_ordProj (K := T.Fr) hp hl hi2
  have u3 := un_nrm (Dw := Dw) c T io hl A.cop w
  have u4 := (un_of_coprime (K := T.Fr) hl A.cop).pow P.totalDegree
  rw [← (((u1.mul u2).mul u3.inv).mul u4).nval e z] at hz1
  convert hz1 using 2
  have h3 := u3.ne
  have h4 := u4.ne
  have h5 : (N : T.Fr) ^ P.totalDegree ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN.pos.ne')
  simp only [map_mul, map_inv₀, map_pow io, map_natCast, Nat.cast_mul, mul_pow] at hz2 ⊢
  generalize (∑ i, hv Xo c nab y.1 (N ^ 2) (F i) P) = Sm at *
  generalize io (nrm Dw c w (A.k : 𝓞 E)) = ν at *
  generalize (A.k : T.Fr) ^ P.totalDegree = κ at *
  generalize (N : T.Fr) ^ P.totalDegree = ξ at *
  have h6 : Sm = κ * ξ * ν⁻¹ * ((κ * ξ)⁻¹ * (ν * Sm)) := by field_simp
  rw [h6, hz2]
  field_simp
end Core

end GlobalTheory.ShortPrime

theorem GlobalTheory.short_value_bound_of_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), Good3 C → ∀ nab : NabV Xo c, IsNab Xo c nab → ∀ (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), 0 < e → ChBound C e ρ w n → ∀ (ℓ : ℕ), ℓ.Prime → ¬ IsUnit (ℓ : T.V) → ∀ (Λ : GenLat E n) (N M : ℕ), Λ.Unimod → Λ.LevOK N M → ∀ (β : c.F), β ≠ 0 → BetaIs (Dw := Dw) c Λ β → ∀ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmL c Λ w → ∀ (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y)))), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo (xOf y) z → (∀ b, tp b ^ (N ^ 2) = 1) → (∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) → AllRat Xo (xOf y) (N ^ 2) → (∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp b ^ m = 1) → letI := io.toAlgebra; ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  intro E _ _ _ H Dw l Xo c _ hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL β hβ0 hβ P hP z tp F hz hg
    htp hF hR ⟨m', hm', htm⟩
  letI := io.toAlgebra
  obtain ⟨J, J', _, _, a, a', σ, hinj, ha, ⟨m, hm, ham⟩, hσ, -⟩ :=
    GlobalTheory.T.isotropic_group_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hp z hz hg
  rw [← Equiv.sum_comp σ, Fintype.sum_prod_type_right, Finset.mul_sum]
  refine GlobalTheory.ShortPrime.le_nval_sum _ _ _ _ fun i' _ => ?_
  choose F₀ h1 h2 h3 using fun b => GlobalTheory.ShortPrime.exists_base Xo hL.1 (sOf1 y) (a' i' b) (tp b) (ham i' b).2 (htp b)
    hm hm' (ham i' b).1 (htm b)
  refine GlobalTheory.ShortPrime.ell_part Xo c hst T io y C hC nab hnab e ρ w n he hB ℓ hp hl Λ N M hU hL β hβ0 hβ P hP hR J a
    hinj ha F₀ (fun i b => sqN Xo N (F (σ (i, i')) b)) h1 h2 fun i b => ?_
  obtain ⟨h4, h5⟩ := (ha _).1 ⟨i, rfl⟩
  exact h3 b _ _ (h5 b) (h4.1 b) (hσ i i' b ▸ hF _ b)
end

section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.ShortBound

section Val
variable {V : Type} {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

theorem vV_one : vV V (1 : K') = 0 := by simp [vV]

theorem vV_pow {x : K'} (hx : x ≠ 0) (n : ℕ) : vV V (x ^ n) = n * vV V x := by
  induction n with
  | zero => simp [vV_one]
  | succ n ih => rw [pow_succ, vV_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem vV_inv {x : K'} (hx : x ≠ 0) : vV V x⁻¹ = - vV V x := by
  have := vV_mul (V := V) hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, vV_one] at this
  omega

theorem vV_nonneg {x : K'} (hx : IsIntegral ℤ x) : 0 ≤ vV V x := by
  have h1 : IsIntegral V x := hx.tower_top
  obtain ⟨a, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := K')).1 h1
  have h2 : valV V (algebraMap V K' a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
  by_cases h0 : algebraMap V K' a = 0
  · simp [vV, h0]
  have := (WithZero.log_le_log (valV_ne_zero h0) one_ne_zero).2 h2
  rw [WithZero.log_one] at this
  simp only [vV]; omega

theorem nval_nonneg (e : ℕ) {x : K'} (hx : IsIntegral ℤ x) : 0 ≤ nval V e x := by
  by_cases h0 : x = 0
  · rw [h0, nval_zero]; exact le_top
  rw [nval_of_ne h0]
  have : (0 : ℝ) ≤ (vV V x : ℝ) := by exact_mod_cast vV_nonneg hx
  exact EReal.coe_nonneg.2 (by positivity)

theorem le_nval_sum (e : ℕ) {J : Type} (s : Finset J) (f : J → K') (a : EReal) (h : ∀ i ∈ s, a ≤ nval V e (f i)) :
    a ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, nval_zero]; exact le_top
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (le_min (h i (Finset.mem_insert_self _ _))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))).trans (nval_add e _ _)

theorem le_nval_avg (e : ℕ) {J : Type} [Finite J] (w X : J → K') (ζ u cc b : K') (m : ℕ) (hm : 0 < m) (hζ : ζ ^ m = 1)
    (hu : u ≠ 0) (hcc : cc ≠ 0) (hw : ∀ q, IsIntegral ℤ (w q)) (ρ : ℝ)
    (hX : ∀ q, ((-ρ : ℝ) : EReal) ≤ nval V e (u * b * X q)) :
    ((-(ρ + (vV V u : ℝ) / e + (vV V cc : ℝ) / e) : ℝ) : EReal) ≤ nval V e (ζ * (cc⁻¹ * b * ∑ᶠ q, w q * X q)) := by
  classical
  have := Fintype.ofFinite J
  have hζ0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hm.ne'] at hζ; exact zero_ne_one hζ
  have hv : vV V ζ = 0 := by
    have := vV_pow (V := V) hζ0 m
    rw [hζ, vV_one] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd (by exact_mod_cast h) hm.ne'
    · exact h
  rw [nval_mul_unit e hζ0 hv, finsum_eq_sum_of_fintype]
  have : cc⁻¹ * b * ∑ q, w q * X q = (cc⁻¹ * u⁻¹) * ∑ q, w q * (u * b * X q) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    field_simp
  rw [this, nval_mul, nval_of_ne (mul_ne_zero (inv_ne_zero hcc) (inv_ne_zero hu)),
    vV_mul (inv_ne_zero hcc) (inv_ne_zero hu), vV_inv hcc, vV_inv hu]
  have h2 : ((-ρ : ℝ) : EReal) ≤ nval V e (∑ q, w q * (u * b * X q)) := by
    refine le_nval_sum e _ _ _ fun q _ => ?_
    rw [nval_mul]
    calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
      _ ≤ _ := add_le_add (nval_nonneg e (hw q)) (hX q)
  refine le_trans (le_of_eq ?_) (add_le_add le_rfl h2)
  rw [← EReal.coe_add]
  congr 1
  push_cast
  ring
end Val

theorem exists_resChar (T : CDVR) (h : T.FinRes) : ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ IsUnit (ℓ : T.V) := by
  haveI : Finite (ResidueField T.V) := h
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField T.V)
  haveI := Fintype.ofFinite (ResidueField T.V)
  refine ⟨p, (CharP.char_is_prime_or_zero (ResidueField T.V) p).resolve_right
    (CharP.char_ne_zero_of_finite (ResidueField T.V) p), fun hu => ?_⟩
  have := hu.map (residue T.V)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem nrm_one (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) : nrm Dw c w 1 = 1 := by simp [nrm]

theorem nrm_mul (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) (a b : 𝓞 E) :
    nrm Dw c w (a * b) = nrm Dw c w a * nrm Dw c w b := by
  simp [nrm, mul_pow, Finset.prod_mul_distrib]

theorem nrm_nat (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) (p : ℕ) :
    nrm Dw c w (p : 𝓞 E) = (p : c.F) ^ Formalism.L2.Pj.DF Dw w := by
  simp [nrm, Formalism.L2.Pj.DF, Finset.prod_pow_eq_pow_sum]

theorem nrm_ne_zero (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) {a : 𝓞 E} (ha : a ≠ 0) : nrm Dw c w a ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
  exact (map_ne_zero (embF c τ)).2 (by simpa using ha)

theorem nrm_integral (c : Coeff l) (w : (E →+* ℂ) × ℕ → ℕ) (a : 𝓞 E) : IsIntegral ℤ (nrm Dw c w a) :=
  IsIntegral.prod _ fun τ _ => ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (embK c τ).toIntAlgHom).pow _

theorem levPt_killed (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : Dw.La) :
    KilledBy Xo l.Mb (levPt Xo x a) := by
  intro b hb
  have := (GlobalTheory.moduli_univ_eta_killed GlobalTheory.firstFiveLaws.1 E H Dw l Xo a).1 b hb
  rw [levPt, Category.assoc, this, MonObj.comp_one]

theorem class_bound (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hch : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hΛ : Λ.Unimod) (hT : Λ.TrivAt l.M) (hN : Λ.LevOK N l.M) (β : c.F) (hβ0 : β ≠ 0) (hβ : BetaIs (Dw := Dw) c Λ β)
    (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b))
    (hR : AllRat Xo (xOf y) (N ^ 2)) (hsq : ¬ ℓ ^ 2 ∣ l.M) (α : 𝓞 E)
    (hα : (¬ ℓ ∣ l.M ∧ α = 1) ∨ (ℓ ∣ l.M ∧ α * H.bar α = (ℓ : 𝓞 E) ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨
      (ℓ ∣ l.M ∧ α = (ℓ : 𝓞 E))) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α) *
      io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [(htp b).1]; exact levPt_killed Xo _ _
  obtain ⟨t1, t2⟩ := GlobalTheory.TorsFac.factorisation E H Dw l Xo N ℓ hN.1 hN.2.1 hℓ
  have lev : ∀ A : ℕ, ℓ ∣ l.M → α * H.bar α = (A : 𝓞 E) →
      ((A = ℓ ∧ l.Mb ≤ Ideal.span {H.bar α}) ∨ (α = (ℓ : 𝓞 E) ∧ ℓ ∣ l.M)) →
      letI := io.toAlgebra
      ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α) *
        io (β⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
          ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
    intro A hd hA hor
    obtain ⟨n', Bn, j, β₀, h1, h2, h3, h4, h5⟩ := t2 α A hA hsq hor
    obtain ⟨k, hk1, hk2⟩ := hT
    rw [← map_mul]
    exact GlobalTheory.PlaceInt.ShortTriv.short_bound_of_trivAt E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hch ℓ hℓ hu Λ N l.M hΛ hN β hβ0 hβ P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF ⟨k, hk1.coprime_dvd_right hd, hk2⟩ n' A Bn j α β₀ h1 h2 hA h3 h4
      (fun b => (h5 _ _ (hk b) (htp b).2).2)
  rcases hα with ⟨hd, rfl⟩ | ⟨hd, hA, hM⟩ | ⟨hd, hA⟩
  · obtain ⟨n', j, -, -, h5⟩ := t1 hd
    rw [nrm_one, map_one, _root_.one_mul]
    choose i hi using fun b => (h5 _ _ (hk b) (htp b).2).2.2
    refine GlobalTheory.short_value_bound_of_coprime E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hch ℓ hℓ hu Λ N l.M hΛ hN β hβ0 hβ P hP z tp F
      hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF hR ⟨l.M ^ (∑ b, i b),
        Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd).symm, fun b => ?_⟩
    obtain ⟨m, hm⟩ : l.M ^ i b ∣ l.M ^ (∑ b, i b) :=
      pow_dvd_pow _ (Finset.single_le_sum (f := i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
    rw [hm, pow_mul, hi b, one_pow]
  · exact lev ℓ hd hA (Or.inl ⟨rfl, hM⟩)
  · exact lev (ℓ ^ 2) hd (by rw [hA, map_natCast]; push_cast; ring) (Or.inr ⟨hA, hd⟩)
end Point

section Run
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons GlobalTheory.PlaceTop

theorem exists_alpha (D : D7) (T : Top D) (h : LawsP T) (hs : LawsSh T) (j : ℕ) (hj : InR D j) (EX : ErrX D)
    (hor : Oriented T EX) (n : ℕ) (w : (D.host.E →+* ℂ) × ℕ → ℕ) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ¬ ℓ ^ 2 ∣ (T.dδ j n).l₂.M ∧ (T.dδ j n).pd ≠ 0 ∧ ∃ α α' : 𝓞 D.host.E,
      α * α' = EX.piG 0 * EX.piG 1 * ((T.dδ j n).pd : 𝓞 D.host.E) ∧ α ≠ 0 ∧ α' ≠ 0 ∧
      ((¬ ℓ ∣ (T.dδ j n).l₂.M ∧ α = 1) ∨
        (ℓ ∣ (T.dδ j n).l₂.M ∧ α * T.Q.H.bar α = (ℓ : 𝓞 D.host.E) ∧ (T.dδ j n).l₂.Mb ≤ Ideal.span {T.Q.H.bar α}) ∨
        (ℓ ∣ (T.dδ j n).l₂.M ∧ α = (ℓ : 𝓞 D.host.E))) := by
  obtain ⟨hdv, hM, hcop, -⟩ := hs.dLev j hj n
  have hM0 : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  obtain ⟨p, hp, hpd⟩ := hs.dPd
  have hpp : (T.dδ j n).pd.Prime := by
    rw [hpd j hj n]
    rcases hp with rfl | rfl
    exacts [D.host.pde_prime, D.host.pde'_prime]
  have hbar := (GlobalTheory.HalfGen.half_principal_and_split D T.toCore h.toLawsM EX).2.1
  have hb : ∀ i, T.Q.H.bar (EX.piG i) = piBarO EX i := fun i => (hbar i).1
  have hn : ∀ i, EX.piG i * T.Q.H.bar (EX.piG i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
    intro i
    apply RingOfIntegers.ext
    rw [hb]
    exact (EX.piG_norm i).trans (by simp)
  have h0 : ∀ i, EX.piG i ≠ 0 := by
    intro i hi
    have := hn i
    rw [hi, zero_mul] at this
    exact (D.host.g_prime i).ne_zero (by exact_mod_cast this.symm)
  have hp0 : (((T.dδ j n).pd : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hsf : Squarefree (T.dδ j n).l₂.M := by
    rw [hM, Nat.squarefree_mul hcop.symm, hM0,
      Nat.squarefree_mul ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)]
    exact ⟨⟨(D.host.g_prime 0).prime.squarefree, (D.host.g_prime 1).prime.squarefree⟩, hpp.prime.squarefree⟩
  refine ⟨fun hd => hℓ.prime.not_unit (hsf ℓ (by rwa [← pow_two])), hpp.ne_zero, ?_⟩
  by_cases hd : ℓ ∣ (T.dδ j n).l₂.M
  · have hd' := hd
    rw [hM, hM0, hℓ.dvd_mul, hℓ.dvd_mul, Nat.prime_dvd_prime_iff_eq hℓ (D.host.g_prime 0),
      Nat.prime_dvd_prime_iff_eq hℓ (D.host.g_prime 1), Nat.prime_dvd_prime_iff_eq hℓ hpp] at hd'
    rcases hd' with (e | e) | e
    · exact ⟨EX.piG 0, EX.piG 1 * _, (mul_assoc _ _ _).symm, h0 0, mul_ne_zero (h0 1) hp0,
        Or.inr (Or.inl ⟨hd, by rw [hn, e], by rw [hb]; exact hdv.2.1.trans (hor 0)⟩)⟩
    · exact ⟨EX.piG 1, EX.piG 0 * _, by ring, h0 1, mul_ne_zero (h0 0) hp0,
        Or.inr (Or.inl ⟨hd, by rw [hn, e], by rw [hb]; exact hdv.2.1.trans (hor 1)⟩)⟩
    · exact ⟨_, EX.piG 0 * EX.piG 1, mul_comm _ _, hp0, mul_ne_zero (h0 0) (h0 1),
        Or.inr (Or.inr ⟨hd, by rw [e]⟩)⟩
  · exact ⟨1, _, _root_.one_mul _, one_ne_zero, mul_ne_zero (mul_ne_zero (h0 0) (h0 1)) hp0, Or.inl ⟨hd, rfl⟩⟩

theorem shortBound : ShortBoundSt := by
  intro D T h hs j hj hinj EX hor w g hg la y
  obtain ⟨hsec, Λ, N, x0, P, hU, hTb, hTM, hN, hadm, hP, hR⟩ := hg
  obtain ⟨Tc, io, e, ho, yI, hy, eta, heta, hq⟩ := y.2
  have hv0 : vAtV y g = nval Tc.V e (evI yI g) := by
    show y.1.1 g = _
    rw [hq]
    rfl
  rw [hv0]
  obtain ⟨inst, hnab⟩ := hs.dNab j hj w.n
  have hlev := hs.dLev j hj w.n
  obtain ⟨hDF, -, -, -, -, -, -, hfin⟩ := GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore h.pins j hj w
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    obtain ⟨h1, h2, -⟩ := h.pins.2.2.2 j hj
    have h3 := hj.1
    have h4 := hj.2
    have h5 := D.R.m_add_three_le_k
    rw [h1, h2]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hrn : D.R.r ≤ w.n := hpq ▸
    (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n)).1 _ x0 hadm
  obtain ⟨ph, ψ, x₀, -, hph, -⟩ := hs.dPhi j hj w.n hrn
  have hwi := GlobalTheory.PlaceInt.datum_isIntegral _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n) hlev ph ψ x₀ hph x0
  obtain ⟨Cls, i1, i2, δ, gdet, hcmp⟩ := hs.dRoot j hj w.n
  obtain ⟨m₀, hm₀, hroot⟩ := GlobalTheory.CoverRoot.value_pow_eq_one _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n) Cls δ gdet hcmp
  have hbe := hs.beta j hj w.n (h.kPsi j hj) Λ hU hTb
  have hβ : betaH (Dw := T.Q.Dw j) T.Q.c Λ ≠ 0 ∧ BetaIs (Dw := T.Q.Dw j) T.Q.c Λ (betaH (Dw := T.Q.Dw j) T.Q.c Λ) := by
    unfold betaH
    rw [dif_pos hbe]
    exact ⟨hbe.choose_spec.1, hbe.choose_spec.2.1⟩
  obtain ⟨ef1, ef2, ef3⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n) Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ (T.Q.Xo j) T.Q.c w.n (T.dδ j w.n) hlev hnab m₀ hroot Λ N hU hTM hN (wtA w) P hP x0 g hsec hR
      Tc io yI hy
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have heR : ((r * e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast he'.ne'
  have hv : ∀ a : T.Q.c.F, vV T'.V (io₂ ((T.dδ j w.n).eF a)) = ((r * e : ℕ) : ℤ) * vLa la a := by
    intro a
    rw [hio]
    exact ho'.2 a
  have hvn : ∀ p : ℕ, vV T'.V (p : T'.Fr) = ((r * e : ℕ) : ℤ) * vLa la (p : T.Q.c.F) := by
    intro p
    rw [← hv, map_natCast, map_natCast]
  rw [← nval_bc iT hr hiT e, hval]
  obtain ⟨ℓ, hℓ, hu⟩ := exists_resChar T' hfr
  obtain ⟨hsq, hp0, α, α', hαb, hα0, hb0, hα⟩ := exists_alpha D T h hs j hj EX hor w.n (wtA w) ℓ hℓ
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ (T.Q.Dw j) _ (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ hnab.1 T' io₂ y₂ C (r * e) he' (wtA w) w.n
    (WeightAlgebra.DF w) hDF.le
  have hcard := GlobalTheory.PlaceInt.card_fun_levQ _ _ (T.Q.Dw j) (T.dδ j w.n).l₂ w.n
  have hM2 : (T.dδ j w.n).l₂.M = D.host.g 0 * D.host.g 1 * (T.dδ j w.n).pd := by
    rw [hlev.2.1, show T.Q.l.M = _ from h.pins.2.1.1]
  have hg0 : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  rw [hfin, hpq, Nat.mul_div_cancel_left _ two_pos, hM2] at hcard
  have hc0 : Nat.card (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) ≠ 0 := by
    rw [hcard]; exact pow_ne_zero _ (mul_ne_zero hg0 hp0)
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) α) ≠ 0 := (map_ne_zero io₂).2 (nrm_ne_zero _ _ hα0)
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ ((T.dδ j w.n).w x0 q)) _ ζ _
    ((Nat.card (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) : ℕ) : T'.Fr) _ m₀ hm₀ hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi q)) _
    (fun q => class_bound (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ (wtA w) w.n he' hch ℓ hℓ
      hu Λ N hU hTM hN _ ((map_ne_zero (T.dδ j w.n).eF).2 hβ.1) (ef1 _ hβ.2) _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi
      (fun b => levRep (q b)) (htp q) (hF q) hrat hsq α hα)
  refine le_trans ?_ (key.trans (le_of_eq ?_))
  · refine EReal.coe_le_coe_iff.2 (neg_le_neg ?_)
    have a1 : ∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) *
        D.host.vdH p * (WeightAlgebra.DF w : ℝ) / 2 = ramLoss D la w := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hvn, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ heR]
    have a2 : vV T'.V ((Nat.card (Fin w.n → LevQ (T.Q.Dw j) (T.dδ j w.n).l₂) : ℕ) : T'.Fr) =
        ((r * e : ℕ) : ℤ) * ((vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) +
          vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F)) * (D.R.f * D.R.r * w.n : ℕ)) := by
      rw [hcard, Nat.cast_pow, vV_pow (by exact_mod_cast mul_ne_zero hg0 hp0), Nat.cast_mul (D.host.g 0 * D.host.g 1),
        vV_mul (by exact_mod_cast hg0) (by exact_mod_cast hp0), hvn, hvn]
      ring
    have a3 : vV T'.V (io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) α)) ≤
        ((r * e : ℕ) : ℤ) * (vLa la ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) +
          vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) * (WeightAlgebra.DF w : ℕ)) := by
      have hπ : EX.piG 0 * EX.piG 1 ≠ 0 := left_ne_zero_of_mul (hαb ▸ mul_ne_zero hα0 hb0)
      have b1 := congrArg (fun a => vV T'.V (io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) a))) hαb
      rw [nrm_mul, nrm_mul _ _ (EX.piG 0 * EX.piG 1), map_mul, map_mul,
        vV_mul hu0 ((map_ne_zero io₂).2 (nrm_ne_zero _ _ hb0)), nrm_nat, map_pow, map_natCast,
        vV_mul ((map_ne_zero io₂).2 (nrm_ne_zero _ _ hπ)) (pow_ne_zero _ (by exact_mod_cast hp0)),
        vV_pow (by exact_mod_cast hp0), hvn, ← ef3 _ (EX.piG 0 * EX.piG 1), hv,
        GlobalTheory.PtTie.nrm_eq_nnW D T h j hj hinj EX w, hDF] at b1
      have b3 : 0 ≤ vV T'.V (io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) α')) :=
        vV_nonneg (map_isIntegral_int io₂ (nrm_integral _ _ _))
      linarith
    have a4 : (vV T'.V (io₂ (nrm (T.Q.Dw j) (T.dδ j w.n).c₂ (wtA w) α)) : ℝ) / (r * e : ℕ) ≤
        ((vLa la ((nnW (recB h.toLawsCore) hinj EX w : 𝓞 T.Q.c.F) : T.Q.c.F) : ℤ) : ℝ) +
          ((vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) * (WeightAlgebra.DF w : ℕ) := by
      rw [div_le_iff₀ (by exact_mod_cast he'), mul_comm]
      exact_mod_cast a3
    rw [a1, a2, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ heR]
    push_cast at a4 ⊢
    linarith
  · congr 3
    simp only [map_mul, map_inv₀, map_natCast]
    ring
end Run

end GlobalTheory.ShortBound
end
end
