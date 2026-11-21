import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KFiniteCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CharacterRegularityFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacterSUTrivialTwo
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeylIntegrationSum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InducedCharacterVanishing
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InducedAdmissibleFiniteLength
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesSUIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleAdmissibleFiniteLength
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsGlobalCharDetPow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraPermute
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraParameterDescent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetUnitScalarMul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryToSpecialUnitaryLocal

section
open Matrix Polynomial GlobalTheory.Orb GlobalTheory.HCChar
open Formalism.REAL (UJ)

namespace GlobalTheory.HCChar

theorem finite_comm_diagonal {n : ℕ} {z : Fin n → ℂ} (hz : Function.Injective z) :
    {M : Matrix (Fin n) (Fin n) ℂ | M * diagonal z = diagonal z * M ∧ M.charpoly = (diagonal z).charpoly}.Finite := by
  refine (Set.finite_range fun f : Fin n → Fin n => diagonal (z ∘ f)).subset ?_
  rintro M ⟨h1, h2⟩
  have hd : M = diagonal fun a => M a a := by
    ext a b
    by_cases hab : a = b
    · simp [hab]
    · have := congrFun (congrFun h1 a) b
      rw [mul_diagonal, diagonal_mul, mul_comm, mul_eq_mul_right_iff] at this
      rw [diagonal_apply_ne _ hab, this.resolve_left fun e => hab (hz e).symm]
  have hr : ∀ a, ∃ b, z b = M a a := fun a => by
    have h3 := congrArg (eval (M a a)) h2
    rw [hd, charpoly_diagonal, charpoly_diagonal, eval_prod, eval_prod,
      Finset.prod_eq_zero (i := a) (by simp) (by simp), eq_comm, Finset.prod_eq_zero_iff] at h3
    obtain ⟨b, -, hb⟩ := h3
    exact ⟨b, by simpa [sub_eq_zero, eq_comm] using hb⟩
  choose f hf using hr
  exact ⟨f, by rw [hd]; exact congrArg diagonal (funext hf)⟩

theorem finite_comm_charpoly {n : ℕ} {S : Matrix (Fin n) (Fin n) ℂ} (hS : IsRegSS S) :
    {M : Matrix (Fin n) (Fin n) ℂ | M * S = S * M ∧ M.charpoly = S.charpoly}.Finite := by
  obtain ⟨z, hz⟩ : ∃ z : Fin n → ℂ, S.charpoly = ∏ a, (X - C (z a)) := by
    have hsp := IsAlgClosed.splits S.charpoly
    have hc : S.charpoly.roots.toList.length = n := by
      rw [Multiset.length_toList, ← hsp.natDegree_eq_card_roots, charpoly_natDegree_eq_dim, Fintype.card_fin]
    have h1 := hsp.eq_prod_roots_of_monic S.charpoly_monic
    rw [← Multiset.coe_toList S.charpoly.roots] at h1
    generalize S.charpoly.roots.toList = l at hc h1
    subst hc
    refine ⟨l.get, h1.trans ?_⟩
    rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    conv_lhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  have hinj : Function.Injective z := by
    rwa [IsRegSS, hz, separable_prod_X_sub_C_iff] at hS
  have he : (diagonal z).charpoly = S.charpoly := by rw [hz, charpoly_diagonal]
  obtain ⟨x, hx⟩ := hS.exists_conj he
  have hD : diagonal z = x * S * (x⁻¹ : GL (Fin n) ℂ) := by rw [← hx, Units.mul_inv_cancel_right]
  refine Set.Finite.of_finite_image (f := fun M => (x : Matrix (Fin n) (Fin n) ℂ) * M * (x⁻¹ : GL (Fin n) ℂ))
    ((finite_comm_diagonal hinj).subset ?_) ?_
  · rintro _ ⟨M, ⟨h1, h2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hD]
      simp only [mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc M, h1, mul_assoc]
    · rw [he, ← h2, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  · intro M _ N _ h
    simpa only [Units.mul_left_inj, Units.mul_right_inj] using h

theorem weylOrder_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (T : Subgroup (UJ ε)), IsCartanSub T → weylOrder T ≠ 0 := by
  rintro n ε T ⟨s, hs, rfl⟩
  have hF := (finite_comm_charpoly hs).to_subtype
  have hinj : Function.Injective (ujMat ε) := Units.val_injective.comp Subtype.val_injective
  let φ : Subgroup.normalizer (cent s : Set (UJ ε)) →
      {M : Matrix (Fin n) (Fin n) ℂ | M * ujMat ε s = ujMat ε s * M ∧ M.charpoly = (ujMat ε s).charpoly} :=
    fun x => ⟨ujMat ε (x * s * x⁻¹), by
      have := mem_cent.1 ((Subgroup.mem_normalizer_iff.1 x.2 s).1 (mem_cent.2 rfl))
      rw [← map_mul, ← map_mul]
      exact congrArg _ this, by
      have := Matrix.charpoly_units_conj x.1.1 (ujMat ε s)
      rw [← Matrix.coe_units_inv] at this
      exact this⟩
  have hφ : ∀ x y, φ x = φ y → x⁻¹ * y ∈ (cent s).subgroupOf (Subgroup.normalizer (cent s : Set (UJ ε))) :=
    fun x y h => by
      have h1 : (x : UJ ε) * s * (x : UJ ε)⁻¹ = y * s * (y : UJ ε)⁻¹ := hinj (congrArg Subtype.val h)
      rw [Subgroup.mem_subgroupOf, mem_cent]
      push_cast
      calc (x : UJ ε)⁻¹ * y * s = (x : UJ ε)⁻¹ * (y * s * (y : UJ ε)⁻¹) * y := by group
        _ = s * ((x : UJ ε)⁻¹ * y) := by rw [← h1]; group
  have : Finite (Subgroup.normalizer (cent s : Set (UJ ε)) ⧸
      (cent s).subgroupOf (Subgroup.normalizer (cent s : Set (UJ ε)))) :=
    Finite.of_injective (fun q => φ q.out) fun q r h => by
      rw [← q.out_eq, ← r.out_eq]
      exact QuotientGroup.eq.2 (hφ _ _ h)
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.HCChar
end

section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_group_order_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (T : Subgroup (UJ ε)), IsCartanSub T → weylOrder T ≠ 0 := by
  atlas_forward_decl GlobalTheory.HCChar.weylOrder_ne_zero
end

section
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CartanFinite

variable {n : ℕ}

theorem exists_scale {G : Matrix (Fin n) (Fin n) ℂ} (hG : Gᴴ = G) {z : Fin n → ℂ} (hz : Function.Injective z)
    (h : (diagonal z)ᴴ * G * diagonal z = G) :
    ∃ d : Fin n → ℂ, (∀ a, d a ≠ 0) ∧ ∀ a b, ((diagonal d)ᴴ * G * diagonal d) a b ∈ ({0, 1, -1} : Finset ℂ) := by
  have h1 : ∀ a b, G a b ≠ 0 → conj (z a) * z b = 1 := fun a b hab => by
    have := congrFun (congrFun h a) b
    rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def] at this
    exact mul_right_cancel₀ hab (by linear_combination this)
  have h2 : ∀ a b, G a b ≠ 0 → ∑ c, G a c = G a b := fun a b hab => by
    refine Finset.sum_eq_single b (fun c _ hc => ?_) (by simp)
    by_contra hac
    have h0 : conj (z a) ≠ 0 := left_ne_zero_of_mul_eq_one (h1 a b hab)
    exact hc (hz (mul_left_cancel₀ h0 ((h1 a c hac).trans (h1 a b hab).symm)))
  have h3 : ∀ a, ∃ d : ℂ, d ≠ 0 ∧ (∑ c, G a c ≠ 0 → d ^ 2 * conj (∑ c, G a c) = 1) := fun a => by
    by_cases h0 : ∑ c, G a c = 0
    · exact ⟨1, one_ne_zero, fun h => absurd h0 h⟩
    · obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (conj (∑ c, G a c))⁻¹ two_pos
      have h0' : conj (∑ c, G a c) ≠ 0 := (map_ne_zero _).2 h0
      refine ⟨d, fun e => inv_ne_zero h0' (by rw [← hd, e]; simp), fun _ => by rw [hd, inv_mul_cancel₀ h0']⟩
  choose d hd0 hd using h3
  refine ⟨d, hd0, fun a b => ?_⟩
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul, Pi.star_apply, Complex.star_def]
  by_cases hab : G a b = 0
  · simp [hab]
  have hba : G b a = conj (G a b) := (congrFun (congrFun hG b) a).symm
  have hba0 : G b a ≠ 0 := by rw [hba]; exact (map_ne_zero _).2 hab
  have ha := hd a (by rwa [h2 a b hab])
  have hb := hd b (by rwa [h2 b a hba0])
  rw [h2 a b hab] at ha
  rw [h2 b a hba0, hba, Complex.conj_conj] at hb
  have ha' := congrArg conj ha
  rw [map_mul, map_pow, Complex.conj_conj, map_one] at ha'
  have : (conj (d a) * G a b * d b) ^ 2 = 1 := by linear_combination (d b ^ 2 * G a b) * ha' + hb
  rcases sq_eq_one_iff.1 this with e | e <;> simp [e]

def IsEigenbasis (s : Matrix (Fin n) (Fin n) ℂ) (g : GL (Fin n) ℂ) : Prop :=
  ∃ z : Fin n → ℂ, Function.Injective z ∧ s * g = g * diagonal z

theorem exists_isEigenbasis {s : Matrix (Fin n) (Fin n) ℂ} (hs : IsRegSS s) : ∃ g, IsEigenbasis s g := by
  have hc : s.charpoly.roots.card = n := by
    rw [← (IsAlgClosed.splits s.charpoly).natDegree_eq_card_roots, charpoly_natDegree_eq_dim, Fintype.card_fin]
  obtain ⟨z, hz⟩ : ∃ z : Fin n → ℂ, s.charpoly.roots = Finset.univ.val.map z := by
    induction' hr : s.charpoly.roots using Quotient.inductionOn with l
    rw [hr] at hc
    obtain rfl : l.length = n := hc
    exact ⟨l.get, by simp⟩
  have he : s.charpoly = (diagonal z).charpoly := by
    rw [charpoly_diagonal, (IsAlgClosed.splits s.charpoly).eq_prod_roots_of_monic s.charpoly_monic, hz,
      Multiset.map_map]
    rfl
  have hd : IsRegSS (diagonal z) := by rwa [IsRegSS, ← he]
  obtain ⟨g, hg⟩ := hd.exists_conj he
  refine ⟨g, z, ?_, hg⟩
  rwa [IsRegSS, charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff] at hd

theorem commute_diagonal {z : Fin n → ℂ} (hz : Function.Injective z) (w : Fin n → ℂ) {u : Matrix (Fin n) (Fin n) ℂ}
    (h : u * diagonal z = diagonal z * u) : u * diagonal w = diagonal w * u := by
  ext a b
  have := congrFun (congrFun h a) b
  rw [mul_diagonal, diagonal_mul] at this ⊢
  by_cases hab : a = b
  · rw [hab, mul_comm]
  · have h0 : u a b = 0 := by
      by_contra h0
      exact hab (hz (mul_left_cancel₀ h0 (by linear_combination -this)))
    simp [h0]

variable {ε : Fin n → Bool}

theorem exists_isEigenbasis_gram {s : UJ ε} (hs : IsRegSS (ujMat ε s)) : ∃ g : GL (Fin n) ℂ,
    IsEigenbasis (ujMat ε s) g ∧ ∀ a b, (g.1ᴴ * Jm ε * g.1) a b ∈ ({0, 1, -1} : Finset ℂ) := by
  obtain ⟨g, z, hz, hg⟩ := exists_isEigenbasis hs
  have hU : (ujMat ε s)ᴴ * Jm ε * ujMat ε s = Jm ε := s.2
  obtain ⟨d, hd0, hd⟩ := exists_scale (G := g.1ᴴ * Jm ε * g.1)
    (by simp [conjTranspose_mul, Jm_conjTranspose, Matrix.mul_assoc]) hz (by
      calc _ = (g.1 * diagonal z)ᴴ * Jm ε * (g.1 * diagonal z) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = g.1ᴴ * ((ujMat ε s)ᴴ * Jm ε * ujMat ε s) * g.1 := by
          simp only [← hg, conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hU])
  let D : GL (Fin n) ℂ := ⟨diagonal d, diagonal fun a => (d a)⁻¹, by simp [hd0], by simp [hd0]⟩
  refine ⟨g * D, ⟨z, hz, ?_⟩, fun a b => ?_⟩
  · change _ * (g.1 * diagonal d) = g.1 * diagonal d * _
    rw [← Matrix.mul_assoc, hg, Matrix.mul_assoc, Matrix.mul_assoc, commute_diagonal hz d (u := diagonal z) rfl]
  · have e : (g.1 * diagonal d)ᴴ * Jm ε * (g.1 * diagonal d) =
        (diagonal d)ᴴ * (g.1ᴴ * Jm ε * g.1) * diagonal d := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← e] at hd
    exact hd a b

theorem conj_mem_cent {s s' x u : UJ ε} {g g' : GL (Fin n) ℂ} (h : IsEigenbasis (ujMat ε s) g)
    (h' : IsEigenbasis (ujMat ε s') g') (hx : x.1 * g = g') (hu : u ∈ cent s) : x * u * x⁻¹ ∈ cent s' := by
  obtain ⟨z, hz, hg⟩ := h
  obtain ⟨w, -, hg'⟩ := h'
  have h1 : ujMat ε u * ujMat ε s = ujMat ε s * ujMat ε u := by
    rw [← map_mul, ← map_mul, GlobalTheory.Orb.mem_cent.1 hu]
  have e : ∀ {t : Matrix (Fin n) (Fin n) ℂ} {k : GL (Fin n) ℂ} {y}, t * k.1 = k.1 * diagonal y →
      diagonal y = (k⁻¹).1 * t * k.1 := fun ht => by rw [Matrix.mul_assoc, ht, Units.inv_mul_cancel_left]
  have h2 := commute_diagonal hz w (u := (g⁻¹).1 * ujMat ε u * g.1) (by
    simp only [e hg, Matrix.mul_assoc, Units.mul_inv_cancel_left]
    rw [← Matrix.mul_assoc (ujMat ε u), h1, Matrix.mul_assoc])
  rw [e hg', ← hx] at h2
  have h3 : (g⁻¹ * u.1 * g) * ((x.1 * g)⁻¹ * s'.1 * (x.1 * g)) = ((x.1 * g)⁻¹ * s'.1 * (x.1 * g)) * (g⁻¹ * u.1 * g) :=
    Units.ext h2
  refine GlobalTheory.Orb.mem_cent.2 (Subtype.ext ?_)
  have h4 := congrArg (fun y => (x.1 * g) * y * (x.1 * g)⁻¹) h3
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  simpa [mul_assoc] using h4

theorem conj_of_gram_eq {s s' : UJ ε} {g g' : GL (Fin n) ℂ} (h : IsEigenbasis (ujMat ε s) g)
    (h' : IsEigenbasis (ujMat ε s') g') (hG : g.1ᴴ * Jm ε * g.1 = g'.1ᴴ * Jm ε * g'.1) :
    ∃ x, (cent s).map (MulAut.conj x).toMonoidHom = cent s' := by
  have hx : g' * g⁻¹ ∈ UJ ε := by
    change (g'.1 * (g⁻¹).1)ᴴ * Jm ε * (g'.1 * (g⁻¹).1) = Jm ε
    calc _ = (g⁻¹).1ᴴ * (g'.1ᴴ * Jm ε * g'.1) * (g⁻¹).1 := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (g.1 * (g⁻¹).1)ᴴ * Jm ε * (g.1 * (g⁻¹).1) := by simp only [← hG, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by simp
  refine ⟨⟨_, hx⟩, le_antisymm ?_ fun u hu => ⟨(⟨_, hx⟩ : UJ ε)⁻¹ * u * (⟨_, hx⟩ : UJ ε)⁻¹⁻¹,
    conj_mem_cent h' h (by simp) hu, by simp [mul_assoc]⟩⟩
  rintro _ ⟨u, hu, rfl⟩
  exact conj_mem_cent h h' (by simp) hu

theorem exists_system {H ι : Type} [Group H] [Finite ι] {P : Subgroup H → Prop} (R : Subgroup H → ι → Prop)
    (h1 : ∀ T, P T → ∃ i, R T i)
    (h2 : ∀ T T' i, R T i → R T' i → ∃ x, T.map (MulAut.conj x).toMonoidHom = T') :
    ∃ 𝒯 : Finset (Subgroup H), (∀ T ∈ 𝒯, P T) ∧
      ∀ T, P T → ∃! T', T' ∈ 𝒯 ∧ ∃ x, T.map (MulAut.conj x).toMonoidHom = T' := by
  classical
  have hm : ∀ (T : Subgroup H) x y, (T.map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      T.map (MulAut.conj (y * x)).toMonoidHom := fun T x y => by
    rw [Subgroup.map_map, map_mul]; rfl
  have h0 : ∀ T : Subgroup H, T.map (MulAut.conj (1 : H)).toMonoidHom = T := fun T => by
    rw [map_one]; exact T.map_id
  let S : Setoid {T // P T} := ⟨fun T T' => ∃ x, T.1.map (MulAut.conj x).toMonoidHom = T'.1,
    fun T => ⟨1, h0 _⟩, fun ⟨x, hx⟩ => ⟨x⁻¹, by rw [← hx, hm, inv_mul_cancel, h0]⟩,
    fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨y * x, by rw [← hm, hx, hy]⟩⟩
  choose f hf using h1
  have : Finite (Quotient S) := Finite.of_injective (fun q : Quotient S => f q.out.1 q.out.2) fun q q' e =>
    Quotient.out_equiv_out.1 (h2 _ _ _ (hf q.out.1 q.out.2)
      ((congrArg (R q'.out.1) e).mpr (hf q'.out.1 q'.out.2)))
  have := Fintype.ofFinite (Quotient S)
  refine ⟨Finset.univ.image fun q : Quotient S => q.out.1, fun T hT => ?_, fun T hT =>
    ⟨(Quotient.mk S ⟨T, hT⟩).out.1, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _),
      S.symm (Quotient.mk_out (s := S) ⟨T, hT⟩)⟩, ?_⟩⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hT
    exact q.out.2
  · rintro T' ⟨hT', hx⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hT'
    rw [Quotient.sound (s := S) (a := ⟨T, hT⟩) (b := q.out) hx, q.out_eq]

theorem exists_isCartanSystem : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ 𝒯 : Finset (Subgroup (UJ ε)), IsCartanSystem 𝒯 := by
  intro n ε
  refine exists_system (ι := Fin n → Fin n → ({0, 1, -1} : Finset ℂ)) (fun T i => ∃ (s : UJ ε) (g : GL (Fin n) ℂ),
    T = cent s ∧ IsEigenbasis (ujMat ε s) g ∧ ∀ a b, (g.1ᴴ * Jm ε * g.1) a b = i a b) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨g, hg, hG⟩ := exists_isEigenbasis_gram hs
    exact ⟨fun a b => ⟨_, hG a b⟩, s, g, rfl, hg, fun _ _ => rfl⟩
  · rintro _ _ i ⟨s, g, rfl, hg, hG⟩ ⟨s', g', rfl, hg', hG'⟩
    exact conj_of_gram_eq hg hg' (Matrix.ext fun a b => (hG a b).trans (hG' a b).symm)

end GlobalTheory.CartanFinite
end
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartan_system : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ 𝒯 : Finset (Subgroup (UJ ε)), IsCartanSystem 𝒯 := by
  atlas_forward_decl GlobalTheory.CartanFinite.exists_isCartanSystem
end

section
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.RealInd
open GlobalTheory.Dec (IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep IsUnitEquiv IsCharFn IsRegSS)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.LowestKTypeDetermines

namespace GlobalTheory.DSCharLowest

theorem isDS_of_cone {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (h : IsSqIntIrr ε σ)
    (h1 : ∃ S : Submodule ℂ V, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S)
    (h2 : ∀ (ν : Fin n → ℝ) (S : Submodule ℂ V), IsKTypeOf ε σ ν S → ∃ c : Fin n → Fin n → ℕ,
      (∀ a b, c a b ≠ 0 → a < b) ∧ ν = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) :
    IsDS ε lam σ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨c1, c2, c3, c4, c5, h1, fun μ S hS => ?_⟩
  obtain ⟨c, hc, rfl⟩ := h2 μ S hS
  unfold vNormSq
  rw [add_right_comm, lowK_add]
  have := nsq_add_cone (strictAnti_add_rho hl.1).antitone hc
  linarith [nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)]

theorem discreteSeriesCharacter_of_parameter : GlobalTheory.Published.IrreducibleUnitaryAdmissible →
    GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.CharacterRegularityFiniteLength →
    GlobalTheory.Published.DiscreteSeriesCharacterOfParameter → GlobalTheory.Dec.DSUnique → GlobalTheory.Published.DiscreteSeriesCharacter := by
  intro hadm han hreg hpar huniq n ε μ _ V _ _ _ lam σ hl hσ hU
  have hA : IsAdmRep ε σ := GlobalTheory.T.admissible_unitary_K_finite.1 hadm n ε V σ hU hσ.2.2.2.1
  have hF := (GlobalTheory.T.irreducible_admissible_finite_length han n ε V σ ⟨hσ.2.1, hA, hσ.2.2.2.1⟩).2
  obtain ⟨Θ, hΘ⟩ := hreg n ε μ V σ hA hF
  obtain ⟨V₀, _, _, _, σ₀, h₀, h1, h2, Θ₀, hΘ₀, hval⟩ := hpar n ε μ lam hl
  obtain ⟨T, hT⟩ := huniq n ε lam V₀ σ₀ V σ hl (isDS_of_cone hl h₀ h1 h2) hσ
  have he : IsUnitEquiv (ujRep h₀.2.2.1) (ujRep hU) := ⟨T, fun g v => hT _ g.2 v⟩
  refine ⟨Θ, hΘ, fun θ hθ => ?_⟩
  rw [← hval θ hθ]
  exact IsCharFn.unique isInducing_matCoord hΘ.1 (hΘ₀.of_isUnitEquiv he) hθ

end GlobalTheory.DSCharLowest
end

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_character_formula : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.CharacterRegularityFiniteLength → GlobalTheory.Published.DiscreteSeriesCharacterOfParameter → GlobalTheory.Dec.DSUnique → GlobalTheory.Published.DiscreteSeriesCharacter := by
  atlas_forward_decl GlobalTheory.DSCharLowest.discreteSeriesCharacter_of_parameter
end

section
noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.HCChar

theorem characterRegularity_of_finiteLength (hA : KFiniteCoefficientsAnalytic)
    (hR : CharacterRegularityFiniteLength) : CharacterRegularity :=
  fun n ε μ _ V _ _ _ π h => hR n ε μ V π h.2.1 (GlobalTheory.T.irreducible_admissible_finite_length hA n ε V π h).2

theorem inducedCharacterSupport_of_vanishing (hR : CharacterRegularityFiniteLength)
    (hV : InducedCharacterVanishing) (hI : InducedAdmissibleFiniteLength) : InducedCharacterSupport := by
  intro n ε μ _ a j W hW hj _ V _ _ _ _ σ h1 h2 s X _ _ _ ρ ι hm h
  obtain ⟨hadm, hfl⟩ := hI n ε a j W hW hj V σ h1 h2 s X ρ ι hm
  obtain ⟨Θ, hΘ⟩ := hR n ε μ X ρ hadm hfl
  obtain ⟨Θ', h3, h4⟩ := hV n ε μ a j W hW hj V σ h1 h2 s X ρ ι hm h
  refine ⟨Θ, hΘ, fun g hg hx => ?_⟩
  rw [hΘ.1.unique isInducing_matCoord h3 hg, h4 g hg hx]

theorem harishChandraCharacters_of_clauses : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CharacterRegularityFiniteLength → GlobalTheory.Published.DiscreteSeriesCharacterOfParameter → GlobalTheory.Published.WeylIntegrationSum → GlobalTheory.Published.InducedCharacterVanishing → GlobalTheory.Published.InducedAdmissibleFiniteLength → GlobalTheory.Published.HarishChandraCharacters :=
  fun hU hA hC hR hD hW hV hI =>
    ⟨characterRegularity_of_finiteLength hA hR,
      GlobalTheory.T.discrete_series_character_formula hU hA hR hD (GlobalTheory.LowestKTypeDetermines.dsUnique_of_dsClass
        (GlobalTheory.Published.discreteSeriesClassification_iff.1 hC)),
      fun n ε => ⟨GlobalTheory.T.exists_cartan_system n ε, GlobalTheory.T.weyl_group_order_ne_zero n ε, fun μ _ => hW n ε μ⟩,
      inducedCharacterSupport_of_vanishing hR hV hI⟩

end GlobalTheory.HCChar

end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ScalarTwist

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem ujMat_scalarMul {n : ℕ} (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    ujMat ε (scalarMul ε (z, g)) = (z : ℂ) • suMat ε g := by
  show umat (GlobalTheory.SqIntSU.unitScalar ε z) * umat (g : UJ ε) = _
  rw [GlobalTheory.SqIntSU.umat_unitScalar, Matrix.smul_mul, Matrix.one_mul]
  rfl

theorem scalar_twist : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure], ∃ c : NNReal, c ≠ 0 ∧ (letI := GlobalTheory.SqIntSU.circleBorelMS; μ = c • Measure.map (scalarMul ε) (circleHaar.prod μ')) ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π') (h : IsURepOn (UJset ε) π), Ext ε m π' π → ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f → repOp (ujRep h) μ f = ((c : ℝ) : ℂ) • repOp (suRep h') μ' fun g : SUJ ε => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar := by
  intro n hn ε μ _ μ' _
  have hn0 : 0 < n := hn
  haveI : SFinite μ' := inferInstance
  haveI : (circleHaar.prod μ').IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  haveI hν : (Measure.map (scalarMul ε) (circleHaar.prod μ')).IsHaarMeasure :=
    Measure.isHaarMeasure_map _ (scalarMul ε) hsc (GlobalTheory.SqIntSU.scalarMul_surjective ε hn0)
      (GlobalTheory.SqIntSU.scalarMul_proper ε)
  set ν := Measure.map (scalarMul ε) (circleHaar.prod μ') with hνdef
  have hmu : μ = μ.haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul μ ν
  have hc0 : μ.haarScalarFactor ν ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ ν).ne'
  refine ⟨μ.haarScalarFactor ν, hc0, hmu, ?_⟩
  intro V _ _ _ m π' π h' h hE f hf hfc
  set c := μ.haarScalarFactor ν
  have hUc : Continuous (ujMat ε) := Units.continuous_val.comp continuous_subtype_val
  have hU : IsUnitaryRep (ujRep h) := GlobalTheory.Orb.isUnitaryRep_repVia h (fun g => g.2) hUc
  have hpt : ∀ (z : Circle) (g : SUJ ε), ujRep h (scalarMul ε (z, g)) = (z : ℂ) ^ m • suRep h' g := by
    intro z g
    show π (ujMat ε (scalarMul ε (z, g))) = (z : ℂ) ^ m • π' (suMat ε g)
    rw [ujMat_scalarMul]
    exact hE z (Circle.norm_coe z) _ (suMat_mem ε g)
  set fm : SUJ ε → ℂ := fun g => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar with hfm
  have hR := hU.isRepOp (μ := μ) hf hfc
  have key : ∀ v, Integrable (fun g => fm g • suRep h' g v) μ' ∧
      ((c : ℂ)⁻¹ • repOp (ujRep h) μ f) v = ∫ g, fm g • suRep h' g v ∂μ' := by
    intro v
    set F : UJ ε → V := fun g => f g • ujRep h g v with hF
    have hFc : Continuous F := hf.smul (hU.continuous_apply v)
    have hFi : Integrable F ν := hFc.integrable_of_hasCompactSupport hfc.smul_right
    have hGi : Integrable (F ∘ scalarMul ε) (circleHaar.prod μ') :=
      (integrable_map_measure hFi.aestronglyMeasurable hsc.aemeasurable).1 hFi
    have hin : ∀ g : SUJ ε, ∫ z, (F ∘ scalarMul ε) (z, g) ∂circleHaar = fm g • suRep h' g v := by
      intro g
      have : ∀ z : Circle, (F ∘ scalarMul ε) (z, g) = (f (scalarMul ε (z, g)) * (z : ℂ) ^ m) • suRep h' g v := by
        intro z
        simp only [Function.comp, hF, hpt, ContinuousLinearMap.smul_apply, smul_smul]
      simp only [this]
      exact integral_smul_const _ _
    refine ⟨?_, ?_⟩
    · have := hGi.integral_prod_right
      simpa only [hin] using this
    · rw [ContinuousLinearMap.smul_apply, (hR v).2]
      conv_lhs => rw [hmu]
      rw [integral_smul_nnreal_measure, hνdef, integral_map hsc.aemeasurable
        (hFc.aestronglyMeasurable),
        show ∫ x, F (scalarMul ε x) ∂(circleHaar.prod μ') = ∫ g, ∫ z, (F ∘ scalarMul ε) (z, g) ∂circleHaar ∂μ' from
          integral_prod_symm _ hGi]
      simp only [hin]
      have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
      rw [NNReal.smul_def, ← Complex.coe_smul, smul_smul, inv_mul_cancel₀ this, one_smul]
  have hT : IsRepOp (suRep h') μ' fm ((c : ℂ)⁻¹ • repOp (ujRep h) μ f) := fun v => ⟨(key v).1, (key v).2⟩
  rw [hT.repOp_eq, smul_smul]
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc0
  simp [this]

end GlobalTheory.ScalarTwist
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CentreAvg

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_finite

variable {n : ℕ}

theorem ujMat_scalarMul (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    ujMat ε (scalarMul ε (z, g)) = (z : ℂ) • suMat ε g := by
  rw [GlobalTheory.SqIntSU.scalarMul_apply, map_mul,
    show ujMat ε (GlobalTheory.SqIntSU.unitScalar ε z) = (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) from rfl,
    Matrix.smul_mul, Matrix.one_mul]
  rfl

theorem matCoord_scalarMul (ε : Fin n → Bool) (z : Circle) (g : SUJ ε) :
    GlobalTheory.Orb.matCoord (ujMat ε) (scalarMul ε (z, g)) = (z : ℂ) • GlobalTheory.Orb.matCoord (suMat ε) g := by
  funext i j
  simp only [GlobalTheory.Orb.matCoord, ujMat_scalarMul, Pi.smul_apply, Matrix.smul_apply]

theorem avg_mem_ccMat : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℤ) (f : UJ ε → ℂ), f ∈ CcMat (ujMat ε) →
    (fun g : SUJ ε => ∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar) ∈ CcMat (suMat ε) := by
  intro n ε m f hf
  obtain ⟨hc, Φ, hΦ, e⟩ := hf
  refine ⟨?_, fun x => ∫ z, (z : ℂ) ^ m * Φ ((z : ℂ) • x) ∂circleHaar, ?_, ?_⟩
  ·
    let W : Set (UJ ε) := (fun p : Circle × UJ ε => (GlobalTheory.SqIntSU.unitScalar ε p.1)⁻¹ * p.2) '' (Set.univ ×ˢ tsupport f)
    have hW : IsCompact W := (isCompact_univ.prod hc.isCompact).image
      (((GlobalTheory.SqIntSU.continuous_unitScalar ε).comp continuous_fst).inv.mul continuous_snd)
    have hT : IsCompact ((Subtype.val : SUJ ε → UJ ε) ⁻¹' W) :=
      (GlobalTheory.SqIntSU.isClosed_special ε).isClosedEmbedding_subtypeVal.isCompact_preimage hW
    refine HasCompactSupport.intro hT fun g hg => ?_
    have h0 : ∀ z : Circle, f (scalarMul ε (z, g)) = 0 := by
      intro z
      refine image_eq_zero_of_notMem_tsupport fun hz => hg ?_
      refine ⟨(z, scalarMul ε (z, g)), ⟨trivial, hz⟩, ?_⟩
      show (GlobalTheory.SqIntSU.unitScalar ε z)⁻¹ * (GlobalTheory.SqIntSU.unitScalar ε z * (g : UJ ε)) = g
      exact inv_mul_cancel_left _ _
    simp only [h0, zero_mul, integral_zero]
  · have hφ : Continuous fun z : Circle => (z : ℂ) ^ m := by
      have : (fun z : Circle => (z : ℂ) ^ m) = fun z : Circle => ((z ^ m : Circle) : ℂ) := by
        funext z; rw [Circle.coe_zpow]
      rw [this]
      exact continuous_subtype_val.comp (continuous_zpow m)
    have hφc : HasCompactSupport fun z : Circle => (z : ℂ) ^ m :=
      HasCompactSupport.intro isCompact_univ fun x hx => (hx (Set.mem_univ x)).elim
    have hO : @OpensMeasurableSpace Circle _ GlobalTheory.SqIntSU.circleBorelMS :=
      @BorelSpace.opensMeasurable Circle _ GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace
    exact @GlobalTheory.Orb.contDiff_integral_param Circle ℂ (Fin n → Fin n → ℂ) _ GlobalTheory.SqIntSU.circleBorelMS hO _ circleHaar _
      _ _ _ _ _ (fun z : Circle => (z : ℂ)) continuous_subtype_val _ hφ hφc
      (fun q : (Fin n → Fin n → ℂ) × ℂ => Φ (q.2 • q.1)) (hΦ.comp (contDiff_snd.smul contDiff_fst))
  · intro g
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [e, matCoord_scalarMul, mul_comm]

end GlobalTheory.CentreAvg
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.CentralCharSU

attribute [local instance] GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special

theorem separable_charpoly_const_smul {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : B.charpoly.Separable) : (c • B).charpoly.Separable := by
  let q : Polynomial ℂ := Polynomial.C c⁻¹ * Polynomial.X
  have key : (c • B).charpoly = Polynomial.C (c ^ Fintype.card (Fin n)) * B.charpoly.comp q := by
    have h1 : B.charpoly.comp q = (B.charmatrix.map (Polynomial.compRingHom q)).det := by
      have := RingHom.map_det (Polynomial.compRingHom q) B.charmatrix
      rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, this]
      rfl
    rw [h1, Polynomial.C_pow, ← Matrix.det_smul, Matrix.charpoly]
    congr 1
    ext i j : 1
    have hcc : Polynomial.C c * (Polynomial.C c⁻¹ * Polynomial.X) = (Polynomial.X : Polynomial ℂ) := by
      rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hc, Polynomial.C_1, one_mul]
    by_cases hij : i = j
    · subst hij
      simp [q, mul_sub, hcc]
    · simp [hij, q]
  have hu : IsUnit (Polynomial.C (c ^ Fintype.card (Fin n))) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hc))
  have hu' : IsUnit (Polynomial.C c⁻¹) := Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hc))
  have h2 : IsCoprime (B.charpoly.comp q) (B.charpoly.derivative.comp q) :=
    IsCoprime.map h (Polynomial.compRingHom q)
  have hq : Polynomial.derivative q = Polynomial.C c⁻¹ := by simp [q]
  rw [key, Polynomial.separable_def, Polynomial.derivative_C_mul, Polynomial.derivative_comp, hq,
    isCoprime_mul_unit_left_left hu, isCoprime_mul_unit_left_right hu, isCoprime_mul_unit_left_right hu']
  exact h2

theorem isRegSS_central_mul {n : ℕ} {ε : Fin n → Bool} {c : SUJ ε} {ζ : ℂ}
    (hc : suMat ε c = ζ • (1 : Matrix (Fin n) (Fin n) ℂ)) {g : SUJ ε} (hg : IsRegSS (suMat ε g)) :
    IsRegSS (suMat ε (c * g)) := by
  have e : suMat ε (c * g) = ζ • suMat ε g := by
    rw [map_mul, hc, Matrix.smul_mul, Matrix.one_mul]
  by_cases hζ : ζ = 0
  · have h01 : (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
      have h := congrArg (· * suMat ε c⁻¹) hc
      simp only [← map_mul, mul_inv_cancel, map_one, hζ, zero_smul, zero_mul] at h
      exact h.symm
    haveI := subsingleton_of_zero_eq_one h01
    rwa [Subsingleton.elim (suMat ε (c * g)) (suMat ε g)]
  · rw [e]
    exact separable_charpoly_const_smul _ ζ hζ hg

theorem continuous_suMat {n : ℕ} (ε : Fin n → Bool) : Continuous (suMat ε) :=
  (isInducing_suMat ε).continuous

theorem charFn_central_mul : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (SUJ ε)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V))
    (h : IsURepOn (SUset ε) π) (Θ : SUJ ε → ℂ), IsCharFn (suMat ε) μ (suRep h) Θ → ∀ (c : SUJ ε) (ζ χ : ℂ),
    suMat ε c = ζ • (1 : Matrix (Fin n) (Fin n) ℂ) → χ ≠ 0 → (∀ v, suRep h c v = χ • v) →
    ∀ g : SUJ ε, IsRegSS (suMat ε g) → Θ (c * g) = χ * Θ g := by
  intro n ε μ _ V _ _ _ π h Θ hΘ c ζ χ hc hχ hv g hg
  haveI := GlobalTheory.DSSU.borelSpace_SUJ ε
  set ρ := suRep h with hρdef
  have hρ : GlobalTheory.OpTrace.IsUnitaryRep ρ := GlobalTheory.Orb.isUnitaryRep_repVia h (suMat_mem ε) (continuous_suMat ε)
  set Θ₂ : SUJ ε → ℂ := fun x => χ⁻¹ * Θ (c * x) with hΘ₂
  have hli : LocallyIntegrable Θ₂ μ := by
    have h0 : LocallyIntegrable (fun x => Θ (c * x)) μ := by
      refine (locallyIntegrable_iff).2 fun K hK => ?_
      have hpre : K = (c * ·) ⁻¹' ((c * ·) '' K) := (Set.preimage_image_eq K (mul_right_injective c)).symm
      rw [hpre]
      exact ((measurePreserving_mul_left μ c).integrableOn_comp_preimage (measurableEmbedding_mulLeft c)).2
        ((locallyIntegrable_iff.1 hΘ.1) _ (hK.image (continuous_mul_left c)))
    exact h0.smul χ⁻¹
  have hcont : ∀ s, IsRegSS (suMat ε s) → ContinuousAt Θ₂ s := fun s hs =>
    continuousAt_const.mul ((hΘ.2.1 (c * s) (isRegSS_central_mul hc hs)).comp (continuous_mul_left c).continuousAt)
  have hΘ₂c : IsCharFn (suMat ε) μ ρ Θ₂ := by
    refine ⟨hli, hcont, fun f hf => ?_⟩
    set f₂ : SUJ ε → ℂ := fun x => f (c⁻¹ * x) with hf₂
    have hf₂m : f₂ ∈ CcMat (suMat ε) := by
      obtain ⟨hs, Φ, hΦ, e⟩ := hf
      refine ⟨hs.comp_homeomorph (Homeomorph.mulLeft c⁻¹), fun x =>
        Φ (fun i j => ∑ k, suMat ε c⁻¹ i k * x k j), ?_, fun x => ?_⟩
      · refine hΦ.comp (contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_)
        exact ContDiff.sum fun k _ => contDiff_const.mul (contDiff_apply_apply ℝ ℂ k j)
      · rw [hf₂]
        simp only [e]
        congr 1
    have hfc : Continuous f := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_suMat ε).continuous hf
    have hf₂c : Continuous f₂ := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_suMat ε).continuous hf₂m
    have hop : repOp ρ μ f₂ = χ • repOp ρ μ f := by
      ext v
      rw [hρ.repOp_apply hf₂c hf₂m.1, ContinuousLinearMap.smul_apply, hρ.repOp_apply hfc hf.1, ← hv,
        ← (ρ c).integral_comp_comm (hρ.isRepOp hfc hf.1 v).1,
        ← integral_mul_left_eq_self (fun x => f₂ x • ρ x v) c]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp [hf₂, map_mul, ContinuousLinearMap.mul_apply]
    have hint : ∫ g, f g * Θ₂ g ∂μ = χ⁻¹ * ∫ g, f₂ g * Θ g ∂μ := by
      rw [← integral_mul_left_eq_self (fun x => f₂ x * Θ x) c, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun x => ?_)
      simp [hf₂, hΘ₂]
      ring
    have ht := hΘ.2.2 f₂ hf₂m
    rw [hop] at ht
    have he : repOp ρ μ f = χ⁻¹ • (χ • repOp ρ μ f) := by rw [smul_smul, inv_mul_cancel₀ hχ, one_smul]
    rw [he, hint]
    exact ⟨ht.1.smul _, by rw [GlobalTheory.OpTrace.trace_smul, ht.2]⟩
  have hu := GlobalTheory.Orb.IsCharFn.unique (isInducing_suMat ε) hΘ₂c hΘ hg
  simp only [hΘ₂] at hu
  rw [← hu]
  field_simp

end GlobalTheory.CentralCharSU
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

namespace GlobalTheory.ExtChar

theorem avgChar_eq_of_ext : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π'), Ext ε m π' π → ∀ Θ' : SUJ ε → ℂ, IsCharFn (suMat ε) μ' (suRep h') Θ' → ∀ g : SUJ ε, IsRegSS (suMat ε g) → GlobalTheory.ExtChar.avgChar ε m Θ' g = Θ' g := by
  intro n _ ε μ' _ V _ _ _ m π' π h' hext Θ' hΘ g hg
  have hcen : ∀ j : ZMod n, Θ' (cen ε j * g) = (((ZMod.toCircle j : Circle) : ℂ) ^ m)⁻¹ * Θ' g := by
    intro j
    set ζ : Circle := ZMod.toCircle j
    have h1mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
      simpa using GlobalTheory.SUChar.suMat_mem ε 1
    have hmat : GlobalTheory.SUChar.suMat ε (cen ε j) = ((ζ : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [suMat_cen]
      show ((ζ⁻¹ : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = _
      rw [Circle.coe_inv]
    have hmem : ((ζ : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := hmat ▸ GlobalTheory.SUChar.suMat_mem ε (cen ε j)
    have hnorm : ‖(ζ : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Circle.norm_coe, inv_one]
    have e1 := hext 1 (by simp) _ hmem
    have e2 := hext (ζ : ℂ)⁻¹ hnorm 1 h1mem
    rw [one_smul, _root_.one_zpow, one_smul] at e1
    have hone : π' 1 = 1 := h'.1.1
    have hrep : ∀ v, GlobalTheory.SUChar.suRep h' (cen ε j) v = ((ζ : ℂ) ^ m)⁻¹ • v := by
      intro v
      show π' (GlobalTheory.SUChar.suMat ε (cen ε j)) v = _
      rw [hmat, ← e1, e2, hone, _root_.inv_zpow]
      rfl
    have hne : ((ζ : ℂ) ^ m)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by simp))
    exact GlobalTheory.CentralCharSU.charFn_central_mul n ε μ' V π' h' Θ' hΘ (cen ε j) _ _ hmat hne hrep g hg
  rw [avgChar]
  have hz : ∀ j : ZMod n, ((ZMod.toCircle j : Circle) : ℂ) ^ m * Θ' (cen ε j * g) = Θ' g := by
    intro j
    rw [hcen, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by simp)), one_mul]
  simp only [hz, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast NeZero.ne n), one_mul]

end GlobalTheory.ExtChar
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar unitScalar)

noncomputable section

namespace GlobalTheory.ExtCharCont

open GlobalTheory.ExtChar Polynomial

theorem charpoly_smul_comp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {c : ℂ} (hc : c ≠ 0) :
    (c • M).charpoly = C (c ^ n) * M.charpoly.comp (C c⁻¹ * X) := by
  apply Polynomial.funext
  intro t
  rw [eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, Matrix.eval_charpoly, Matrix.eval_charpoly]
  have h := Matrix.det_smul (Matrix.scalar (Fin n) (c⁻¹ * t) - M) c
  rw [Fintype.card_fin] at h
  rw [← h]
  congr 1
  ext i j
  simp [Matrix.scalar_apply, Matrix.sub_apply, Matrix.diagonal_apply, mul_sub]
  split_ifs <;> field_simp

theorem isRegSS_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {c : ℂ} (hc : c ≠ 0) (h : IsRegSS M) :
    IsRegSS (c • M) := by
  unfold IsRegSS at *
  obtain ⟨a, b, hab⟩ := h
  rw [charpoly_smul_comp M hc]
  have h1 := congrArg (fun p : ℂ[X] => p.comp (C c⁻¹ * X)) hab
  simp only [add_comp, mul_comp, one_comp] at h1
  refine ⟨C (c ^ n)⁻¹ * a.comp (C c⁻¹ * X), C (c ^ n)⁻¹ * C c * b.comp (C c⁻¹ * X), ?_⟩
  have e1 : (C (c ^ n)⁻¹ * C (c ^ n) : ℂ[X]) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hc), C_1]
  have e2 : (C c * C c⁻¹ : ℂ[X]) = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hc, C_1]
  rw [derivative_C_mul, derivative_comp, derivative_C_mul, derivative_X, mul_one]
  linear_combination h1 + (a.comp (C c⁻¹ * X) * M.charpoly.comp (C c⁻¹ * X) +
    C c * C c⁻¹ * b.comp (C c⁻¹ * X) * (derivative M.charpoly).comp (C c⁻¹ * X)) * e1 +
    b.comp (C c⁻¹ * X) * (derivative M.charpoly).comp (C c⁻¹ * X) * e2

variable {n : ℕ} (ε : Fin n → Bool)

theorem umat_mul' (a b : UJ ε) : umat (a * b) = umat a * umat b := rfl

theorem continuousAt_detRoot_one : ContinuousAt (detRoot ε) 1 := by
  have h1 : Continuous fun g : UJ ε => (umat g).det :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_det
  have h2 : (umat (1 : UJ ε)).det ∈ Complex.slitPlane := by
    have : umat (1 : UJ ε) = 1 := rfl
    rw [this, Matrix.det_one]
    exact Complex.one_mem_slitPlane
  have h3 : ContinuousAt (fun g : UJ ε => Complex.arg (umat g).det) 1 :=
    ContinuousAt.comp (f := fun g : UJ ε => (umat g).det) (Complex.continuousAt_arg h2) h1.continuousAt
  exact Circle.exp.continuous.continuousAt.comp (h3.div_const _)

def locRoot (s y : UJ ε) : Circle := detRoot ε s * detRoot ε (s⁻¹ * y)

theorem continuousAt_locRoot (s : UJ ε) : ContinuousAt (locRoot ε s) s := by
  have h : ContinuousAt (fun y : UJ ε => detRoot ε (s⁻¹ * y)) s := by
    exact (continuousAt_detRoot_one ε).comp_of_eq ((continuous_const.mul continuous_id).continuousAt (x := s))
      (inv_mul_cancel s)
  exact continuousAt_const.mul h

variable [NeZero n]

theorem locRoot_pow (s y : UJ ε) : ((locRoot ε s y : Circle) : ℂ) ^ n = (umat y).det := by
  rw [locRoot, Circle.coe_mul, mul_pow, detRoot_pow ε (NeZero.ne n), detRoot_pow ε (NeZero.ne n),
    ← Matrix.det_mul, ← umat_mul', mul_inv_cancel_left]

def locPart (s y : UJ ε) : SUJ ε :=
  ⟨unitScalar ε (locRoot ε s y)⁻¹ * y, by
    show (umat (unitScalar ε (locRoot ε s y)⁻¹ * y)).det = 1
    rw [det_unitScalar_mul, Circle.coe_inv, inv_pow, locRoot_pow, inv_mul_cancel₀]
    intro h0
    have := GlobalTheory.SqIntSU.norm_det_umat ε y
    rw [h0, norm_zero] at this
    exact zero_ne_one this⟩

theorem continuousAt_locPart (s : UJ ε) : ContinuousAt (locPart ε s) s := by
  rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
  show ContinuousAt (fun y => unitScalar ε (locRoot ε s y)⁻¹ * y) s
  exact ((GlobalTheory.SqIntSU.continuous_unitScalar ε).continuousAt.comp (continuousAt_locRoot ε s).inv).mul continuousAt_id

theorem scalarMul_loc (s y : UJ ε) : scalarMul ε (locRoot ε s y, locPart ε s y) = y := by
  show unitScalar ε (locRoot ε s y) * (unitScalar ε (locRoot ε s y)⁻¹ * y) = y
  rw [← unitScalar_inv, mul_inv_cancel_left]

theorem isRegSS_unitScalar_mul (z : Circle) (y : UJ ε) (h : IsRegSS (ujMat ε y)) :
    IsRegSS (ujMat ε (unitScalar ε z * y)) := by
  have e : ujMat ε (unitScalar ε z * y) = (z : ℂ) • ujMat ε y := by
    show (z : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * ujMat ε y = _
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [e]
  exact isRegSS_smul _ (Circle.coe_ne_zero z) h

theorem continuousAt_avgChar (m : ℤ) (Θ' : SUJ ε → ℂ)
    (hΘ : ∀ g : SUJ ε, IsRegSS (suMat ε g) → ContinuousAt Θ' g) (g : SUJ ε) (hg : IsRegSS (suMat ε g)) :
    ContinuousAt (avgChar ε m Θ') g := by
  unfold avgChar
  refine continuousAt_const.mul (tendsto_finset_sum _ fun j _ => ?_)
  have h : ContinuousAt (fun x : SUJ ε => Θ' (cen ε j * x)) g :=
    ContinuousAt.comp (f := fun x : SUJ ε => cen ε j * x)
      (hΘ _ (isRegSS_unitScalar_mul ε (ZMod.toCircle j)⁻¹ (g : UJ ε) hg))
      (continuous_const.mul continuous_id).continuousAt
  exact continuousAt_const.mul h

theorem continuousAt_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (m : ℤ) (Θ' : SUJ ε → ℂ), (∀ g : SUJ ε, IsRegSS (suMat ε g) → ContinuousAt Θ' g) → ∀ s : UJ ε, IsRegSS (ujMat ε s) → ContinuousAt (GlobalTheory.ExtChar.extChar ε m Θ') s := by
  intro n _ ε m Θ' hΘ s hs
  have e : extChar ε m Θ' = fun y => ((locRoot ε s y : Circle) : ℂ) ^ m * avgChar ε m Θ' (locPart ε s y) := by
    funext y
    rw [← extChar_scalarMul, scalarMul_loc]
  rw [e]
  have h1 : ContinuousAt (fun y => ((locRoot ε s y : Circle) : ℂ)) s :=
    continuous_subtype_val.continuousAt.comp (continuousAt_locRoot ε s)
  refine (h1.zpow₀ m (Or.inl (Circle.coe_ne_zero _))).mul ?_
  exact ContinuousAt.comp (f := locPart ε s)
    (continuousAt_avgChar ε m Θ' hΘ _ (isRegSS_unitScalar_mul ε (locRoot ε s s)⁻¹ s hs))
    (continuousAt_locPart ε s)

end GlobalTheory.ExtCharCont

end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

variable {n : ℕ} (ε : Fin n → Bool)

theorem measurable_detRoot : Measurable (detRoot (n := n) ε) := by
  have hdet : Continuous fun x : UJ ε => (umat x).det :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_det
  have h1 : Measurable fun x : UJ ε => Complex.arg (umat x).det / (n : ℝ) :=
    (Complex.measurable_arg.comp hdet.measurable).div_const _
  exact Circle.exp.continuous.measurable.comp h1

variable [NeZero n]

theorem measurable_root (j : ZMod n) : Measurable fun x : UJ ε => root ε x j :=
  (measurable_detRoot ε).mul_const _

theorem measurable_part (j : ZMod n) : Measurable fun x : UJ ε => part ε x j := by
  have hc : Continuous fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2 :=
    ((GlobalTheory.SqIntSU.continuous_unitScalar ε).comp ((continuous_fst.mul continuous_const).inv)).mul continuous_snd
  have hp : Measurable fun x : UJ ε => (detRoot ε x, x) := (measurable_detRoot ε).prodMk measurable_id
  have hcomp : Measurable ((fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2) ∘ fun x : UJ ε => (detRoot ε x, x)) :=
    hc.measurable.comp hp
  have he : (fun x : UJ ε => GlobalTheory.SqIntSU.unitScalar ε (root ε x j)⁻¹ * x) = ((fun p : Circle × UJ ε =>
      GlobalTheory.SqIntSU.unitScalar ε (p.1 * ZMod.toCircle j)⁻¹ * p.2) ∘ fun x : UJ ε => (detRoot ε x, x)) := by
    funext x; simp only [Function.comp_apply, root]
  have hm : Measurable fun x : UJ ε => GlobalTheory.SqIntSU.unitScalar ε (root ε x j)⁻¹ * x := he ▸ hcomp
  exact hm.subtype_mk

theorem measurable_extChar (m : ℤ) (Θ : SUJ ε → ℂ) (hΘ : Measurable Θ) : Measurable (extChar ε m Θ) := by
  have hz : Continuous fun z : Circle => (z : ℂ) ^ m :=
    Continuous.zpow₀ (by fun_prop) m (fun z => Or.inl (Circle.coe_ne_zero z))
  unfold extChar
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun j _ => ?_
  exact (hz.measurable.comp (measurable_root ε j)).mul (hΘ.comp (measurable_part ε j))

end GlobalTheory.ExtChar

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem aestronglyMeasurable_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), AEStronglyMeasurable Θ' μ' → AEStronglyMeasurable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
  intro n _ ε μ' _ m Θ' hΘ
  have hm'' : Measurable (hΘ.mk Θ') := hΘ.stronglyMeasurable_mk.measurable
  have hae : ∀ᵐ g ∂μ', Θ' g = hΘ.mk Θ' g := hΘ.ae_eq_mk
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hE : MeasurableSet (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) :=
    MeasurableSet.iUnion fun j => measurable_part ε j hNm
  have hpre : scalarMul ε ⁻¹' (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) ⊆
      ⋃ k : ZMod n, Set.univ ×ˢ ((fun g => cen ε k * g) ⁻¹' N) := by
    rintro ⟨z, g⟩ hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    obtain ⟨i, hi⟩ := root_scalarMul ε z g
    refine Set.mem_iUnion.2 ⟨i + j, Set.mem_univ _, ?_⟩
    have h := part_scalarMul ε z g i hi j
    simp only [Set.mem_preimage] at hj ⊢
    rw [h] at hj
    exact hj
  have hE0 : Measure.map (scalarMul ε) (circleHaar.prod μ') (⋃ j : ZMod n, (fun x => part ε x j) ⁻¹' N) = 0 := by
    rw [Measure.map_apply (GlobalTheory.SqIntSU.continuous_scalarMul ε).measurable hE]
    refine measure_mono_null hpre (measure_iUnion_null fun k => ?_)
    rw [Measure.prod_prod, measure_preimage_mul, hN0, mul_zero]
  have heq : extChar ε m (hΘ.mk Θ') =ᵐ[Measure.map (scalarMul ε) (circleHaar.prod μ')] extChar ε m Θ' := by
    refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hE0)
    by_contra hxE
    apply hx
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hxE
    simp only [extChar]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : Θ' (part ε x j) = hΘ.mk Θ' (part ε x j) := by
      by_contra h
      exact hxE j (hsub h)
    rw [h]
  exact (measurable_extChar ε m _ hm'').aestronglyMeasurable.congr heq

end GlobalTheory.ExtChar
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

namespace GlobalTheory.ExtChar

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special

theorem integrableOn_translate {n : ℕ} (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure]
    (Θ' : SUJ ε → ℂ) (h : LocallyIntegrable Θ' μ') (c : SUJ ε) {K : Set (SUJ ε)} (hK : IsCompact K) :
    IntegrableOn (fun g => Θ' (c * g)) K μ' := by
  have h1 : IntegrableOn Θ' ((fun g => c * g) '' K) μ' :=
    h.integrableOn_isCompact (hK.image (continuous_const.mul continuous_id))
  have h2 := ((measurePreserving_mul_left μ' c).integrableOn_comp_preimage
    (MeasurableEquiv.mulLeft c).measurableEmbedding).2 h1
  exact h2.mono_set (Set.subset_preimage_image _ _)

theorem integrableOn_avgChar {n : ℕ} [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure]
    (m : ℤ) (Θ' : SUJ ε → ℂ) (h : LocallyIntegrable Θ' μ') {K : Set (SUJ ε)} (hK : IsCompact K) :
    IntegrableOn (avgChar ε m Θ') K μ' := by
  unfold avgChar
  exact (integrable_finset_sum _ fun j _ => (integrableOn_translate ε μ' Θ' h _ hK).const_mul _).const_mul _

theorem locallyIntegrable_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), LocallyIntegrable Θ' μ' → AEStronglyMeasurable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) → LocallyIntegrable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
  intro n _ ε μ' _ m Θ' h hm
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  rw [locallyIntegrable_iff]
  intro K hK
  have hP : IsCompact (scalarMul ε ⁻¹' K) := by
    have := (isProperMap_iff_tendsto_cocompact.2 ⟨hsc, GlobalTheory.SqIntSU.scalarMul_proper ε⟩)
    exact this.isCompact_preimage hK
  have hK' : IsCompact (Prod.snd '' (scalarMul ε ⁻¹' K)) := hP.image continuous_snd
  have hmr := hm.restrict (s := K)
  rw [IntegrableOn]
  rw [Measure.restrict_map hsc.measurable hK.measurableSet] at hmr ⊢
  rw [integrable_map_measure hmr hsc.measurable.aemeasurable]
  have hz : Integrable (fun z : Circle => (z : ℂ) ^ m) circleHaar := by
    have hc : Continuous (fun z : Circle => (z : ℂ) ^ m) :=
      (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).zpow₀ m fun z => Or.inl (Circle.coe_ne_zero z)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 := hz.mul_prod (integrableOn_avgChar ε μ' m Θ' h hK')
  have h2 : IntegrableOn (fun p : Circle × SUJ ε => (p.1 : ℂ) ^ m * avgChar ε m Θ' p.2)
      (Set.univ ×ˢ (Prod.snd '' (scalarMul ε ⁻¹' K))) (circleHaar.prod μ') := by
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
    exact h1
  have h3 := h2.mono_set (t := _) (s := scalarMul ε ⁻¹' K) fun p hp => ⟨trivial, p, hp, rfl⟩
  have e : extChar ε m Θ' ∘ scalarMul ε = fun p : Circle × SUJ ε => (p.1 : ℂ) ^ m * avgChar ε m Θ' p.2 := by
    funext p
    exact extChar_scalarMul ε m Θ' p.1 p.2
  rw [e]
  exact h3

end GlobalTheory.ExtChar
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtCharInt

attribute [local instance] GlobalTheory.SqIntSU.circleBorelMS GlobalTheory.SqIntSU.circleBorelSpace GlobalTheory.SqIntSU.circleHaar_isHaar
  GlobalTheory.SqIntSU.circleHaar_finite GlobalTheory.SqIntSU.locallyCompact_special GlobalTheory.SqIntSU.secondCountable_special
  GlobalTheory.SqIntSU.sigmaCompact_special GlobalTheory.DSSU.borelSpace_SUJ

theorem scalarMul_cen {n : ℕ} [NeZero n] (ε : Fin n → Bool) (j : ZMod n) (z : Circle) (g : SUJ ε) :
    scalarMul ε (z * ZMod.toCircle j, GlobalTheory.ExtChar.cen ε j * g) = scalarMul ε (z, g) := by
  rw [GlobalTheory.SqIntSU.scalarMul_apply, GlobalTheory.SqIntSU.scalarMul_apply]
  show GlobalTheory.SqIntSU.unitScalar ε (z * ZMod.toCircle j) *
      (GlobalTheory.SqIntSU.unitScalar ε (ZMod.toCircle j)⁻¹ * (g : UJ ε)) = _
  rw [← mul_assoc, ← GlobalTheory.SqIntSU.unitScalar_mul, mul_inv_cancel_right]

theorem locallyIntegrable_snd {n : ℕ} (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [SFinite μ'] (Θ' : SUJ ε → ℂ)
    (h : LocallyIntegrable Θ' μ') :
    LocallyIntegrable (fun p : Circle × SUJ ε => Θ' p.2) (circleHaar.prod μ') := by
  intro x
  obtain ⟨U, hU, hi⟩ := h x.2
  refine ⟨Set.univ ×ˢ U, prod_mem_nhds Filter.univ_mem hU, ?_⟩
  rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
  exact hi.comp_snd circleHaar

theorem integral_extChar : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (m : ℤ) (Θ' : SUJ ε → ℂ), LocallyIntegrable Θ' μ' → LocallyIntegrable (GlobalTheory.ExtChar.extChar ε m Θ') (letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) → ∀ f : UJ ε → ℂ, Continuous f → HasCompactSupport f → ∫ x, f x * GlobalTheory.ExtChar.extChar ε m Θ' x ∂(letI := GlobalTheory.SqIntSU.circleBorelMS; Measure.map (scalarMul ε) (circleHaar.prod μ')) = ∫ g, (∫ z, f (scalarMul ε (z, g)) * (z : ℂ) ^ m ∂circleHaar) * Θ' g ∂μ' := by
  intro n _ ε μ' _ m Θ' hΘ hE f hf hfc
  haveI : SFinite μ' := inferInstance
  have hsc : Continuous (scalarMul ε) := GlobalTheory.SqIntSU.continuous_scalarMul ε
  have hI : Integrable (fun x => f x * GlobalTheory.ExtChar.extChar ε m Θ' x)
      (Measure.map (scalarMul ε) (circleHaar.prod μ')) := by
    simpa only [smul_eq_mul] using hE.integrable_smul_left_of_hasCompactSupport hf hfc
  rw [integral_map hsc.aemeasurable hI.aestronglyMeasurable]

  set G : Circle × SUJ ε → ℂ := fun p => f (scalarMul ε p) * (p.1 : ℂ) ^ m * Θ' p.2 with hGdef
  have hzc : Continuous fun z : Circle => (z : ℂ) ^ m :=
    Continuous.zpow₀ continuous_subtype_val m (fun z => Or.inl (Circle.coe_ne_zero z))
  have hc : Continuous fun p : Circle × SUJ ε => f (scalarMul ε p) * (p.1 : ℂ) ^ m :=
    (hf.comp hsc).mul (hzc.comp continuous_fst)
  have hprop : IsProperMap (scalarMul ε) :=
    isProperMap_iff_tendsto_cocompact.2 ⟨hsc, GlobalTheory.SqIntSU.scalarMul_proper ε⟩
  have hcs : HasCompactSupport fun p : Circle × SUJ ε => f (scalarMul ε p) * (p.1 : ℂ) ^ m := by
    refine HasCompactSupport.intro (hprop.isCompact_preimage hfc) fun p hp => ?_
    have : f (scalarMul ε p) = 0 := image_eq_zero_of_notMem_tsupport hp
    simp [this]
  have hG : Integrable G (circleHaar.prod μ') := by
    simpa only [smul_eq_mul, hGdef] using
      (locallyIntegrable_snd ε μ' Θ' hΘ).integrable_smul_left_of_hasCompactSupport hc hcs

  have hT : ∀ j : ZMod n, MeasurePreserving (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g)) (circleHaar.prod μ') (circleHaar.prod μ') := fun j =>
    (measurePreserving_mul_right circleHaar _).prod (measurePreserving_mul_left μ' _)
  have hEmb : ∀ j : ZMod n, MeasurableEmbedding (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g)) := fun j =>
    ((MeasurableEquiv.mulRight (ZMod.toCircle j)).prodCongr
      (MeasurableEquiv.mulLeft (GlobalTheory.ExtChar.cen ε j))).measurableEmbedding
  have hpt : ∀ p : Circle × SUJ ε, f (scalarMul ε p) * GlobalTheory.ExtChar.extChar ε m Θ' (scalarMul ε p) =
      (n : ℂ)⁻¹ * ∑ j : ZMod n, G (Prod.map (fun z : Circle => z * ZMod.toCircle j)
        (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g) p) := by
    rintro ⟨z, g⟩
    rw [GlobalTheory.ExtChar.extChar_scalarMul, GlobalTheory.ExtChar.avgChar, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hGdef, Prod.map, scalarMul_cen, Circle.coe_mul, mul_zpow]
    ring
  simp only [hpt]
  rw [integral_const_mul, integral_finset_sum (f := fun j p => G (Prod.map (fun z : Circle => z * ZMod.toCircle j)
      (fun g : SUJ ε => GlobalTheory.ExtChar.cen ε j * g) p)) _ (fun j _ => ((hT j).integrable_comp_emb (hEmb j)).2 hG)]
  simp only [fun j => (hT j).integral_comp (hEmb j) G]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne n)), one_mul, integral_prod_symm G hG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [hGdef]
  exact integral_mul_const _ _

end GlobalTheory.ExtCharInt
end
end

section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

noncomputable section

namespace GlobalTheory.ExtChar

theorem exists_isCharFn_ext : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π') (h : IsURepOn (UJset ε) π), Ext ε m π' π → ∀ Θ' : SUJ ε → ℂ, IsCharFn (suMat ε) μ' (suRep h') Θ' → ∃ Θ : UJ ε → ℂ, IsCharFn (ujMat ε) μ (ujRep h) Θ ∧ ∀ (z : Circle) (g : SUJ ε), IsRegSS (suMat ε g) → Θ (scalarMul ε (z, g)) = (z : ℂ) ^ m * Θ' g := by
  intro n hn ε μ _ μ' _ V _ _ _ m π' π h' h hE Θ' hΘ'
  haveI : NeZero n := ⟨by omega⟩
  letI := GlobalTheory.SqIntSU.circleBorelMS
  obtain ⟨c, hc0, hμ, hop⟩ := GlobalTheory.ScalarTwist.scalar_twist n hn ε μ μ'
  have hmeas := GlobalTheory.ExtChar.aestronglyMeasurable_extChar n ε μ' m Θ' hΘ'.1.aestronglyMeasurable
  have hli := GlobalTheory.ExtChar.locallyIntegrable_extChar n ε μ' m Θ' hΘ'.1 hmeas
  refine ⟨GlobalTheory.ExtChar.extChar ε m Θ', ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hμ]
    intro x
    obtain ⟨s, hs, hi⟩ := hli x
    exact ⟨s, hs, by rw [IntegrableOn, Measure.restrict_smul]; exact hi.smul_measure ENNReal.coe_ne_top⟩
  · exact GlobalTheory.ExtCharCont.continuousAt_extChar n ε m Θ' hΘ'.2.1
  · intro f hf
    have hfc : Continuous f := GlobalTheory.Orb.continuous_of_mem_ccSmooth (isInducing_matCoord (ε := ε)).continuous hf
    rw [hop V m π' π h' h hE f hfc hf.1]
    have ht := hΘ'.2.2 _ (GlobalTheory.CentreAvg.avg_mem_ccMat n ε m f hf)
    refine ⟨ht.1.smul _, ?_⟩
    rw [OpTrace.trace_smul, ht.2, hμ, integral_smul_nnreal_measure, GlobalTheory.ExtCharInt.integral_extChar n ε μ' m Θ' hΘ'.1 hli f hfc hf.1,
      NNReal.smul_def, Complex.real_smul]
  · intro z g hg
    rw [GlobalTheory.ExtChar.extChar_scalarMul, GlobalTheory.ExtChar.avgChar_eq_of_ext n ε μ' V m π' π h' hE Θ' hΘ' g hg]

end GlobalTheory.ExtChar
end
end

section
noncomputable section

namespace GlobalTheory.DSUFromSU.Small

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.HCChar GlobalTheory.FormalDegree.Model
open GlobalTheory.Dec (IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep IsCharFn IsRegSS)

def Concl {n : ℕ} (ε : Fin n → Bool) (μ : Measure (UJ ε)) (lam : Fin n → ℝ) : Prop :=
  ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
    (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h : IsSqIntIrr ε σ),
    (∃ S : Submodule ℂ V, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S) ∧
    (∀ (ν : Fin n → ℝ) (S : Submodule ℂ V), IsKTypeOf ε σ ν S → ∃ c : Fin n → Fin n → ℕ,
      (∀ a b, c a b ≠ 0 → a < b) ∧ ν = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
    ∃ Θ, IsCharFn (ujMat ε) μ (ujRep h.2.2.1) Θ ∧
      ∀ θ : Fin n → ℝ, IsRegSS (ujMat ε (torusPt ε θ)) → Θ (torusPt ε θ) = dsChar ε lam θ

theorem diag_mem_K {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    (diagonal fun a => Complex.exp (θ a * Complex.I)) ∈ Kset ε := by
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, ?_⟩
  · rw [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp
  · simp only [Jm, diagonal_mul_diagonal, mul_comm]

theorem wt_unique {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (ℂ →L[ℂ] ℂ)) {ν ν' : Fin n → ℝ}
    {v v' : ℂ} (hv : v ≠ 0) (hv' : v' ≠ 0) (h : IsWtOn (Kset ε) σ ν v) (h' : IsWtOn (Kset ε) σ ν' v') : ν = ν' := by
  have key : ∀ θ : Fin n → ℝ, Complex.exp ((∑ a, ν a * θ a : ℝ) * Complex.I) =
      Complex.exp ((∑ a, ν' a * θ a : ℝ) * Complex.I) := fun θ => by
    have e := h θ (diag_mem_K ε θ)
    have e' := h' θ (diag_mem_K ε θ)
    set T := σ (diagonal fun a => Complex.exp (θ a * Complex.I))
    have t : ∀ w : ℂ, T w = T 1 * w := fun w => by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    rw [t, smul_eq_mul] at e e'
    exact (mul_right_cancel₀ hv e).symm.trans (mul_right_cancel₀ hv' e')
  funext a
  by_contra hne
  have hd : ν a - ν' a ≠ 0 := sub_ne_zero.2 hne
  have := key (Pi.single a (Real.pi / (ν a - ν' a)))
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  have e : ν a * (Real.pi / (ν a - ν' a)) = ν' a * (Real.pi / (ν a - ν' a)) + Real.pi := by field_simp; ring
  rw [e, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at this
  exact Complex.exp_ne_zero _ (by linear_combination (-1 / 2 : ℂ) * this)

theorem concl_detPow (n : ℕ) (s : Bool) (m : ℤ) (μ : Measure (UJ fun _ : Fin n => s)) [μ.IsHaarMeasure] :
    Formalism.QuantumDeterminants.IsHCParam (lamDet n m) ∧ Concl (fun _ : Fin n => s) μ (lamDet n m) := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.HCChar.Model.ds_case n s m μ
  obtain ⟨Θ, h3, h4⟩ := h2 h1.2.2.1
  refine ⟨h0, ℂ, inferInstance, inferInstance, inferInstance, detPow n m,
    ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1⟩, h1.2.2.2.2.2.1, fun ν S hS => ⟨0, by simp, ?_⟩, Θ, h3.1, h4⟩
  obtain ⟨S', hS'⟩ := h1.2.2.2.2.2.1
  obtain ⟨v, -, hv, hw⟩ := hS.2.2.2.1
  obtain ⟨v', -, hv', hw'⟩ := hS'.2.2.2.1
  simpa using wt_unique _ _ hv hv' hw hw'

theorem rank_zero (ε : Fin 0 → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (lam : Fin 0 → ℝ) : Concl ε μ lam := by
  obtain rfl : ε = fun _ => true := Subsingleton.elim _ _
  obtain rfl : lam = lamDet 0 0 := Subsingleton.elim _ _
  exact (concl_detPow 0 true 0 μ).2

theorem rank_one (ε : Fin 1 → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (lam : Fin 1 → ℝ)
    (h : Formalism.QuantumDeterminants.IsHCParam lam) : Concl ε μ lam := by
  obtain ⟨s, rfl⟩ : ∃ s, ε = fun _ => s := ⟨ε 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  obtain ⟨m, hm⟩ := h.2 0
  obtain rfl : lam = lamDet 1 m := by
    funext a
    rw [Subsingleton.elim a 0]
    simp [lamDet, Formalism.QuantumDeterminants.rhoStd] at hm ⊢
    exact hm
  exact (concl_detPow 1 s m μ).2

end GlobalTheory.DSUFromSU.Small

end

noncomputable section

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.HCChar GlobalTheory.SUChar GlobalTheory.Published
open GlobalTheory.Orb (ujMat ujRep IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset IsParS IsParU IsHCS IsHCU Ext exists_isHaarMeasure_SUJ)
open GlobalTheory.DSId (IsHCDS)
open GlobalTheory.SqIntSU (scalarMul unitScalar)

namespace GlobalTheory.DSUFromSU

variable {n : ℕ}

theorem isRegSS_diagonal_iff (d : Fin n → ℂ) : IsRegSS (diagonal d) ↔ Function.Injective d := by
  rw [IsRegSS, charpoly_diagonal, Polynomial.separable_prod_X_sub_C_iff]

theorem isRegSS_diagonal_mul (d : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    IsRegSS (diagonal d) → IsRegSS (diagonal fun a => d a * c) := by
  rw [isRegSS_diagonal_iff, isRegSS_diagonal_iff]
  exact fun h a b e => h (mul_right_cancel₀ hc e)

theorem torusPt_eq_scalarMul (ε : Fin n → Bool) (θ : Fin n → ℝ) (φ : ℝ) (h : ∑ a, (θ a - φ) = 0) :
    torusPt ε θ = scalarMul ε (Circle.exp φ, suTorusPt ε (fun a => θ a - φ) h) := by
  apply Subtype.ext
  apply Units.ext
  show diagonal (fun a => Complex.exp (θ a * Complex.I)) =
    (Circle.exp φ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun a => Complex.exp (((θ a - φ : ℝ) : ℂ) * Complex.I))
  rw [Matrix.smul_mul, Matrix.one_mul, ← diagonal_smul]
  congr 1
  funext a
  rw [Pi.smul_apply, smul_eq_mul, Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem weylDenom_sub_const (θ : Fin n → ℝ) (φ : ℝ) : weylDenom (fun a => θ a - φ) = weylDenom θ := by
  simp only [weylDenom, sub_sub_sub_cancel_right]

theorem wtVal_twist (hn : n ≠ 0) (lam θ : Fin n → ℝ) (m : ℤ) (hm : ∑ a, lam a = m) (w : Equiv.Perm (Fin n)) :
    wtVal (lam ∘ w.symm) θ = (Circle.exp ((∑ a, θ a) / n) : ℂ) ^ m *
      wtVal ((fun a => lam a - (m : ℝ) / n) ∘ w.symm) (fun a => θ a - (∑ b, θ b) / n) := by
  have hsum : ∑ a, lam (w.symm a) = m := by rw [Equiv.sum_comp w.symm lam]; exact hm
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [Circle.coe_exp, wtVal, wtVal, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  have key : (∑ a, (lam ∘ w.symm) a * θ a) = (m : ℝ) * ((∑ a, θ a) / n) +
      ∑ a, ((fun a => lam a - (m : ℝ) / n) ∘ w.symm) a * (θ a - (∑ b, θ b) / n) := by
    simp only [Function.comp_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsum]
    field_simp
    ring
  rw [key]
  push_cast
  ring

theorem dsChar_twist (ε : Fin n → Bool) (hn : n ≠ 0) (lam θ : Fin n → ℝ) (m : ℤ) (hm : ∑ a, lam a = m) :
    dsChar ε lam θ = (Circle.exp ((∑ a, θ a) / n) : ℂ) ^ m *
      dsChar ε (fun a => lam a - (m : ℝ) / n) (fun a => θ a - (∑ b, θ b) / n) := by
  simp only [dsChar, wtVal_twist hn lam θ m hm, weylDenom_sub_const]
  have : ∀ s : Finset (Equiv.Perm (Fin n)), ∀ (c : ℂ) (f g : Equiv.Perm (Fin n) → ℂ),
      ∑ w ∈ s, f w * (c * g w) = c * ∑ w ∈ s, f w * g w := fun s c f g => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  rw [this]
  ring

end GlobalTheory.DSUFromSU

namespace GlobalTheory.DSUFromSU

theorem discreteSeriesCharacterOfParameter (hP : DiscreteSeriesCharacterSU) : DiscreteSeriesCharacterOfParameter := by
  intro n ε μ _ lam hlam
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · exact Small.rank_zero ε μ lam
    · exact Small.rank_one ε μ lam hlam
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hU : IsParU lam := ⟨hlam.1.injective, hlam.2⟩
  obtain ⟨m, hm, hS, -⟩ := GlobalTheory.SUtoU.extension_main n hn1 ε ℂ (fun _ => 0) lam hU
  obtain ⟨μ', hμ'⟩ := exists_isHaarMeasure_SUJ ε
  obtain ⟨V, i1, i2, i3, σ, hσ, Θ', hΘ', hform⟩ := hP n hn ε μ' _ hS
  obtain ⟨m2, hm2, -, hext⟩ := GlobalTheory.SUtoU.extension_main n hn1 ε V σ lam hU
  have e : m2 = m := by exact_mod_cast hm2.symm.trans hm
  rw [e] at hext
  obtain ⟨π, hE, hHC⟩ := hext hσ
  have hDS : IsHCDS ε lam π := by
    have h := GlobalTheory.DSSU.Chamber.vChamber n ε V π lam 1 (fun a b h _ => h) hlam.1 hHC
    simpa only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Function.comp_id, Matrix.submatrix_id_id] using h
  obtain ⟨Θ, hΘ, hΘf⟩ := GlobalTheory.ExtChar.exists_isCharFn_ext n hn1 ε μ μ' V m σ π hσ.1.2.2.1 hDS.1.2.2.1 hE Θ' hΘ'
  refine ⟨V, i1, i2, i3, π, hDS.1, hDS.2.2.1.exists, hDS.2.2.2, Θ, hΘ, fun θ hreg => ?_⟩
  have hθ' : ∑ a, (θ a - (∑ b, θ b) / n) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hreg' : IsRegSS (suMat ε (suTorusPt ε (fun a => θ a - (∑ b, θ b) / n) hθ')) := by
    rw [suMat_suTorusPt]
    rw [ujMat_torusPt] at hreg
    have h := isRegSS_diagonal_mul _ (Complex.exp_ne_zero ((-((∑ b, θ b) / n : ℝ) : ℂ) * Complex.I)) hreg
    convert h using 3 with a
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hanti : StrictAnti fun a => lam a - (m : ℝ) / n := fun a b h => sub_lt_sub_right (hlam.1 h) _
  rw [torusPt_eq_scalarMul ε θ _ hθ', hΘf _ _ hreg', hform _ hθ' hreg', chamberChar_of_strictAnti ε hanti,
    dsChar_twist ε hn0 lam θ m hm]

end GlobalTheory.DSUFromSU
end
end

section
namespace GlobalTheory.HarishChandraCharacterSU

theorem harishChandraCharacters_SU_of_hypotheses :
    GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic →
    GlobalTheory.Published.DiscreteSeriesSU → GlobalTheory.Published.CharacterRegularityFiniteLength →
    GlobalTheory.Published.DiscreteSeriesCharacterSU → GlobalTheory.Published.WeylIntegrationSum →
    GlobalTheory.Published.InducedCharacterVanishing → GlobalTheory.Published.InducedAdmissibleFiniteLength →
    GlobalTheory.Published.HarishChandraCharacters :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 =>
    GlobalTheory.HCChar.harishChandraCharacters_of_clauses h1 h2 (GlobalTheory.DSSU.FromSU.discreteSeriesClassification_of_SU h3) h4 (GlobalTheory.DSUFromSU.discreteSeriesCharacterOfParameter h5) h6 h7 h8

end GlobalTheory.HarishChandraCharacterSU
end
