import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LieInj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepBasisCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsomComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrEmbeddingDeterminantValue
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulEqZeroOfToCompletion
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSandwichTraceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieNumberFieldPointStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdivGroupForPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieHodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichStarRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateKernelAtPointStatement

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section

namespace GlobalTheory.PlaceRing

open IsDedekindDomain NumberField ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen GlobalTheory.EigenLieCompare

theorem mem_maximalIdeal_iff_norm_lt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) :
    x ∈ IsLocalRing.maximalIdeal 𝓞_ℂ_[p] ↔ ‖(x : ℂ_[p])‖ < 1 := by
  have hv : (Valued.v : Valuation ℂ_[p] _).Integers 𝓞_ℂ_[p] :=
    Valuation.valuationSubring.integers _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one, ← ne_eq,
    ← (hv.map_le_one x).lt_iff_ne]
  change Valued.v (x : ℂ_[p]) < 1 ↔ _
  rw [← GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.valuation_coe_eq_norm, NNReal.coe_lt_one]

theorem natCast_mem_maximalIdeal (p : ℕ) [Fact p.Prime] :
    ((p : ℕ) : 𝓞_ℂ_[p]) ∈ IsLocalRing.maximalIdeal 𝓞_ℂ_[p] := by
  rw [mem_maximalIdeal_iff_norm_lt]
  have h : (((p : ℕ) : 𝓞_ℂ_[p]) : ℂ_[p]) = ((p : ℕ) : ℂ_[p]) := by push_cast; rfl
  rw [h, GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.norm_p]
  exact GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.inv_p_lt_one p

theorem exists_padicInt_hom (p : ℕ) [Fact p.Prime] : Nonempty (ℤ_[p] →+* 𝓞_ℂ_[p]) :=
  ⟨((algebraMap ℚ_[p] ℂ_[p]).comp (PadicInt.Coe.ringHom (p := p))).codRestrict 𝓞_ℂ_[p]
    fun x => by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.mem_iff_norm]
      change ‖algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p])‖ ≤ 1
      rw [norm_algebraMap']
      exact x.2⟩

theorem faithfulSMul_Ow (p : ℕ) [Fact p.Prime] {E : Type} [Field E] [NumberField E]
    {w : HeightOneSpectrum (𝓞 E)} [Algebra ℤ_[p] (Ow w)] : FaithfulSMul ℤ_[p] (Ow w) := by
  rw [faithfulSMul_iff_algebraMap_injective, RingHom.injective_iff_ker_eq_bot]
  by_contra h
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p h
  have h1 : ((p : ℤ_[p]) ^ n) ∈ RingHom.ker (algebraMap ℤ_[p] (Ow w)) := by
    rw [hn]; exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at h1
  have h2 : ((p : ℕ) : Ow w) ≠ 0 := by
    intro h0
    have h3 := congrArg (fun y : Ow w => Valued.v (algebraMap (Ow w) (w.adicCompletion E) y)) h0
    rw [← map_natCast (algebraMap (𝓞 E) (Ow w)), valued_algebraMap, map_zero, map_zero] at h3
    exact w.intValuation_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) h3
  exact pow_ne_zero n h2 h1

theorem exists_placeRing : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (τ₀ : NumberField.RingOfIntegers E →+* 𝓞_ℂ_[p]), ∃ (Λ : Type) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsDiscreteValuationRing Λ) (_ : Algebra ℤ_[p] Λ) (_ : Module.Finite ℤ_[p] Λ) (_ : FaithfulSMul ℤ_[p] Λ) (π : ℤ_[p] ⊗[ℤ] NumberField.RingOfIntegers E →ₐ[ℤ_[p]] Λ) (e : ℤ_[p] ⊗[ℤ] NumberField.RingOfIntegers E) (t₀ : Λ →+* 𝓞_ℂ_[p]), IsIdempotentElem e ∧ Function.Surjective π ∧ RingHom.ker π = Ideal.span {1 - e} ∧ (∀ a, t₀ (π (1 ⊗ₜ a)) = τ₀ a) ∧ ∀ τ : NumberField.RingOfIntegers E →+* 𝓞_ℂ_[p], (∀ a, ‖(τ a : ℂ_[p])‖ < 1 ↔ ‖(τ₀ a : ℂ_[p])‖ < 1) → ∃ t : Λ →+* 𝓞_ℂ_[p], ∀ a, t (π (1 ⊗ₜ a)) = τ a := by
  intro E _ _ p _ τ₀
  obtain ⟨φ⟩ := exists_padicInt_hom p
  letI : Algebra ℤ_[p] 𝓞_ℂ_[p] := φ.toAlgebra
  have hpP : (p : 𝓞 E) ∈ (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap τ₀ := by
    rw [Ideal.mem_comap, map_natCast]
    exact natCast_mem_maximalIdeal p
  obtain ⟨w, hwP⟩ : ∃ w : HeightOneSpectrum (𝓞 E),
      w.asIdeal = (IsLocalRing.maximalIdeal 𝓞_ℂ_[p]).comap τ₀ := by
    refine ⟨⟨_, Ideal.comap_isPrime _ _, fun h => ?_⟩, rfl⟩
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hpP
    exact (Fact.out : p.Prime).ne_zero hpP
  have hw : GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.IsOver p w := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.IsOver
    rwa [hwP]
  obtain ⟨_, -⟩ := exists_toCompletion hw
  obtain ⟨e, he⟩ := exists_isPlaceIdem hw
  let π : ℤ_[p] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[p]] Ow w := tauExt (p := p) (algebraMap (𝓞 E) (Ow w))
  have hπ : Function.Surjective π := toCompletion_surjective hw
  have hπe : π e = 1 := tauExt_eq_one hw he _ (mem_iff_algebraMap w)
  have hker : RingHom.ker π = Ideal.span {1 - e} := by
    ext x
    constructor
    · intro hx
      have h : e * x = 0 := mul_eq_zero_of_toCompletion hw he hx
      exact Ideal.mem_span_singleton'.2 ⟨x, by linear_combination -h⟩
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
      rw [RingHom.mem_ker, map_mul, map_sub, map_one, hπe, sub_self, mul_zero]
  have hext : ∀ τ : 𝓞 E →+* 𝓞_ℂ_[p], (∀ a, ‖(τ a : ℂ_[p])‖ < 1 ↔ ‖(τ₀ a : ℂ_[p])‖ < 1) →
      ∃ t : Ow w →+* 𝓞_ℂ_[p], ∀ a, t (π (1 ⊗ₜ a)) = τ a := by
    intro τ hτ
    have h1 : tauExt (p := p) τ e = 1 := tauExt_eq_one hw he τ fun a => by
      rw [hwP, Ideal.mem_comap, mem_maximalIdeal_iff_norm_lt, mem_maximalIdeal_iff_norm_lt, hτ]
    have hk : RingHom.ker π.toRingHom ≤ RingHom.ker (tauExt (p := p) τ).toRingHom := by
      intro x hx
      have hx' : x ∈ Ideal.span {1 - e} := hker ▸ hx
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
      change tauExt (p := p) τ (a * (1 - e)) = 0
      rw [map_mul, map_sub, map_one, h1, sub_self, mul_zero]
    refine ⟨π.toRingHom.liftOfSurjective hπ ⟨(tauExt (p := p) τ).toRingHom, hk⟩, fun a => ?_⟩
    exact (RingHom.liftOfRightInverse_comp_apply π.toRingHom _ _
      ⟨(tauExt (p := p) τ).toRingHom, hk⟩ (1 ⊗ₜ a)).trans (tauExt_toPadic τ a)
  obtain ⟨t₀, ht₀⟩ := hext τ₀ fun _ => Iff.rfl
  exact ⟨Ow w, inferInstance, inferInstance, inferInstance, inferInstance,
    Module.Finite.of_surjective π.toLinearMap hπ, faithfulSMul_Ow p, π, e, t₀, he.1, hπ, hker, ht₀,
    hext⟩

end GlobalTheory.PlaceRing
end
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem idempotent_matrix_split_of_isLocalRing (A : Type) [CommRing A] [IsLocalRing A] (h : ℕ)
    (X : Matrix (Fin h) (Fin h) A) : X * X = X → ∃ (n : ℕ) (i : Matrix (Fin h) (Fin n) A)
      (q : Matrix (Fin n) (Fin h) A), q * i = 1 ∧ i * q = X ∧ X.trace = n := by
  classical
  intro hX
  set f : (Fin h → A) →ₗ[A] (Fin h → A) := Matrix.toLin' X with hfdef
  have hff : ∀ v, f (f v) = f v := by
    intro v
    have : Matrix.toLin' (X * X) v = Matrix.toLin' X v := by rw [hX]
    simpa [Matrix.toLin'_mul, hfdef] using this
  set M := LinearMap.range f
  have hsplit : f.rangeRestrict ∘ₗ M.subtype = LinearMap.id := by
    ext ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := hw
    simp [hff]
  haveI : Module.Projective A M := Module.Projective.of_split M.subtype f.rangeRestrict hsplit
  haveI : Module.Free A M := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis A M
  have hqi : LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) *
      LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) ∘ₗ (M.subtype ∘ₗ b.equivFun.symm.toLinearMap)
        = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      have h1 : f.rangeRestrict (M.subtype (b.equivFun.symm v)) = b.equivFun.symm v :=
        LinearMap.congr_fun hsplit _
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    rw [this, LinearMap.toMatrix'_id]
  have hiq : LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) *
      LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict) = X := by
    rw [← LinearMap.toMatrix'_comp]
    have : (M.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict)
        = f := by
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rfl
    rw [this, hfdef, LinearMap.toMatrix'_toLin']
  refine ⟨Module.finrank A M, LinearMap.toMatrix' (M.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ f.rangeRestrict), hqi, hiq, ?_⟩
  rw [← hiq, Matrix.trace_mul_comm, hqi, Matrix.trace_one, Fintype.card_fin]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_matrix_local_split : ∀ (A : Type) [CommRing A] [IsLocalRing A] (h : ℕ) (X : Matrix (Fin h) (Fin h) A), X * X = X → ∃ (n : ℕ) (i : Matrix (Fin h) (Fin n) A) (q : Matrix (Fin n) (Fin h) A), q * i = 1 ∧ i * q = X ∧ X.trace = n := by
  atlas_forward_decl GlobalTheory.idempotent_matrix_split_of_isLocalRing
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

def cornerHom {Γ R : Type} [CommRing Γ] [CommRing R] {h n : ℕ}
    (ρ : Γ →+* Matrix (Fin h) (Fin h) R) (e : Γ) (i : Matrix (Fin h) (Fin n) R)
    (q : Matrix (Fin n) (Fin h) R) (hqi : q * i = 1) (hiq : i * q = ρ e) :
    Γ →+* Matrix (Fin n) (Fin n) R where
  toFun x := q * ρ x * i
  map_one' := by simp [hqi]
  map_mul' x y := by
    have h1 : q * ρ e = q := by rw [← hiq, ← Matrix.mul_assoc, hqi, Matrix.one_mul]
    have h2 : ρ x * ρ e = ρ e * ρ x := by rw [← map_mul, ← map_mul, mul_comm]
    calc q * ρ (x * y) * i = (q * ρ e) * (ρ x * ρ y) * i := by rw [h1, map_mul]
      _ = q * (ρ x * ρ e) * ρ y * i := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = q * ρ x * i * (q * ρ y * i) := by rw [← hiq]; simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]

theorem corner_lift {Γ Λ R : Type} [CommRing Γ] [CommRing Λ] [CommRing R] {h n : ℕ}
    (π : Γ →+* Λ) (hπ : Function.Surjective π) (e : Γ) (hk : RingHom.ker π = Ideal.span {1 - e})
    (ρ : Γ →+* Matrix (Fin h) (Fin h) R) (i : Matrix (Fin h) (Fin n) R)
    (q : Matrix (Fin n) (Fin h) R) (hqi : q * i = 1) (hiq : i * q = ρ e) :
    ∃ ρ' : Λ →+* Matrix (Fin n) (Fin n) R, ∀ x, ρ' (π x) = q * ρ x * i := by
  have hker : RingHom.ker π ≤ RingHom.ker (cornerHom ρ e i q hqi hiq) := by
    rw [hk, Ideal.span_le, Set.singleton_subset_iff]
    show cornerHom ρ e i q hqi hiq (1 - e) = 0
    rw [map_sub, map_one]
    show 1 - q * ρ e * i = 0
    rw [← hiq, ← Matrix.mul_assoc, hqi, Matrix.one_mul, hqi, sub_self]
  exact ⟨π.liftOfSurjective hπ ⟨_, hker⟩, fun x => π.liftOfRightInverse_comp_apply _ _ ⟨_, hker⟩ x⟩

theorem phiInv_ofPadic_apply (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (c : ℤ_[p]) :
    phiInv p O (ofPadic p O c) = ofPadic p O c := by
  unfold phiInv ofPadic
  ext n
  simp only [RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (Subsingleton.elim
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p))) (ZMod.castHom (dvd_refl p) (PreTilt O p))) _

theorem datum_idempotent_part : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (π : Γ →ₐ[ℤ_[p]] Λ) (e : Γ), IsIdempotentElem e → Function.Surjective π → RingHom.ker π = Ideal.span {1 - e} → ∀ (h : ℕ) (D : Datum ε h Γ), ∃ (h' : ℕ) (D' : Datum ε h' Λ) (iT : Matrix (Fin h) (Fin h') ℤ_[p]) (pT : Matrix (Fin h') (Fin h) ℤ_[p]) (iM : Matrix (Fin h) (Fin h') (Ainf p O)) (pM : Matrix (Fin h') (Fin h) (Ainf p O)), pT * iT = 1 ∧ iT * pT = D.ρT e ∧ pM * iM = 1 ∧ iM * pM = D.ρM e ∧ D'.F = pM * D.F * iT.map (ofPadic p O) ∧ D'.G = pT.map (ofPadic p O) * D.G * iM ∧ (∀ x, D'.ρT (π x) = pT * D.ρT x * iT) ∧ ∀ x, D'.ρM (π x) = pM * D.ρM x * iM := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Γ _ _ Λ _ _ π e he hπ hk h D
  obtain ⟨hdom, hloc, -, -, hν, hξ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  obtain ⟨-, -, -, hΨ, hΨ'⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Γ h D
  have hμ : mu ε ≠ 0 := by
    rw [← xi_mul_nu]
    refine mul_ne_zero hξ ?_
    intro h0
    exact hν (by rw [h0, map_zero])
  obtain ⟨n, iT, pT, hT1, hT2, hT3⟩ := GlobalTheory.T.idempotent_matrix_local_split ℤ_[p] h (D.ρT e) (by rw [← map_mul, he.eq])
  obtain ⟨n', iM, pM, hM1, hM2, hM3⟩ :=
    GlobalTheory.T.idempotent_matrix_local_split (Ainf p O) h (D.ρM e) (by rw [← map_mul, he.eq])
  have htr := (GlobalTheory.T.matrix_sandwich_trace_eq (Ainf p O) h (mu ε) D.F D.G _ _ hμ D.G_mul_F (D.F_act e)).2.2
  have hnn : n' = n := by
    have h1 : ((D.ρT e).map (ofPadic p O)).trace = (n : Ainf p O) := by
      rw [← AddMonoidHom.map_trace (ofPadic p O), hT3, map_natCast]
    rw [hM3, h1] at htr
    have h2 := congrArg (fun x => algebraMap O C (WittVector.fontaineTheta O p x)) htr
    simpa using h2
  subst hnn
  obtain ⟨rT, hrT⟩ := corner_lift (π : Γ →+* Λ) hπ e hk (D.ρT : Γ →+* _) iT pT hT1 hT2
  obtain ⟨rM, hrM⟩ := corner_lift (π : Γ →+* Λ) hπ e hk D.ρM iM pM hM1 hM2
  have hrT' : ∀ x, rT (π x) = pT * D.ρT x * iT := hrT
  have hrM' : ∀ x, rM (π x) = pM * D.ρM x * iM := hrM
  have hpM : pM * D.ρM e = pM := by rw [← hM2, ← Matrix.mul_assoc, hM1, Matrix.one_mul]
  have hiM : D.ρM e * iM = iM := by rw [← hM2, Matrix.mul_assoc, hM1, Matrix.mul_one]
  have hiT : D.ρT e * iT = iT := by rw [← hT2, Matrix.mul_assoc, hT1, Matrix.mul_one]
  have hφ : (iT.map (ofPadic p O)).map (phiInv p O) = iT.map (ofPadic p O) := by
    ext1 i j
    simp only [Matrix.map_apply, phiInv_ofPadic_apply]
  have hφe : iM.map (phiInv p O) * pM.map (phiInv p O) = (D.ρM e).map (phiInv p O) := by
    rw [← Matrix.map_mul, hM2]
  refine ⟨n',
    { F := pM * D.F * iT.map (ofPadic p O)
      G := pT.map (ofPadic p O) * D.G * iM
      Ψ := pM * D.Ψ * iM.map (phiInv p O)
      Ψ' := pM.map (phiInv p O) * D.Ψ' * iM
      ρT := { rT with
        commutes' := by
          intro c
          show rT (algebraMap ℤ_[p] Λ c) = _
          rw [← π.commutes, hrT', AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
            Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hT1] }
      ρM := rM
      G_mul_F := ?_
      F_eq := ?_
      Ψ_mul := ?_
      F_act := ?_ }, iT, pT, iM, pM, hT1, hT2, hM1, hM2, rfl, rfl, hrT', hrM'⟩
  · calc pT.map (ofPadic p O) * D.G * iM * (pM * D.F * iT.map (ofPadic p O))
        = pT.map (ofPadic p O) * D.G * ((iM * pM) * D.F) * iT.map (ofPadic p O) := by
          simp only [Matrix.mul_assoc]
      _ = pT.map (ofPadic p O) * (D.G * D.F) * ((D.ρT e).map (ofPadic p O) * iT.map (ofPadic p O)) := by
          rw [hM2, ← D.F_act e]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [← Matrix.map_mul, hiT, D.G_mul_F, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
            ← Matrix.map_mul, hT1, Matrix.map_one _ (map_zero _) (map_one _)]
  · symm
    calc pM * D.Ψ * iM.map (phiInv p O) * (pM * D.F * iT.map (ofPadic p O)).map (phiInv p O)
        = pM * (D.Ψ * (iM.map (phiInv p O) * pM.map (phiInv p O))) * D.F.map (phiInv p O) *
            iT.map (ofPadic p O) := by
          rw [Matrix.map_mul, Matrix.map_mul, hφ]; simp only [Matrix.mul_assoc]
      _ = (pM * D.ρM e) * (D.Ψ * D.F.map (phiInv p O)) * iT.map (ofPadic p O) := by
          rw [hφe, hΨ]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hpM, ← D.F_eq]
  · calc pM * D.Ψ * iM.map (phiInv p O) * (pM.map (phiInv p O) * D.Ψ' * iM)
        = pM * D.Ψ * ((iM.map (phiInv p O) * pM.map (phiInv p O)) * D.Ψ') * iM := by
          simp only [Matrix.mul_assoc]
      _ = pM * (D.Ψ * D.Ψ') * (D.ρM e * iM) := by
          rw [hφe, ← hΨ']; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hiM, D.Ψ_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hM1]
  · intro a
    obtain ⟨x, rfl⟩ := hπ a
    show _ * (rT (π x)).map (ofPadic p O) = rM (π x) * _
    have hc : D.ρM e * D.ρM x = D.ρM x * D.ρM e := by rw [← map_mul, ← map_mul, mul_comm]
    rw [hrT', hrM']
    calc pM * D.F * iT.map (ofPadic p O) * (pT * D.ρT x * iT).map (ofPadic p O)
        = pM * (D.F * (iT * pT).map (ofPadic p O)) * (D.ρT x).map (ofPadic p O) *
            iT.map (ofPadic p O) := by
          simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = pM * D.ρM e * (D.F * (D.ρT x).map (ofPadic p O)) * iT.map (ofPadic p O) := by
          rw [hT2, D.F_act e]; simp only [Matrix.mul_assoc]
      _ = pM * (D.ρM e * D.ρM x) * D.F * iT.map (ofPadic p O) := by
          rw [D.F_act x]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hc, ← hM2]; simp only [Matrix.mul_assoc]

end GlobalTheory.DetInv
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_quotient_datum_compat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (π : Γ →ₐ[ℤ_[p]] Λ) (e : Γ), IsIdempotentElem e → Function.Surjective π → RingHom.ker π = Ideal.span {1 - e} → ∀ (h : ℕ) (D : Datum ε h Γ), ∃ (h' : ℕ) (D' : Datum ε h' Λ) (iT : Matrix (Fin h) (Fin h') ℤ_[p]) (pT : Matrix (Fin h') (Fin h) ℤ_[p]) (iM : Matrix (Fin h) (Fin h') (Ainf p O)) (pM : Matrix (Fin h') (Fin h) (Ainf p O)), pT * iT = 1 ∧ iT * pT = D.ρT e ∧ pM * iM = 1 ∧ iM * pM = D.ρM e ∧ D'.F = pM * D.F * iT.map (ofPadic p O) ∧ D'.G = pT.map (ofPadic p O) * D.G * iM ∧ (∀ x, D'.ρT (π x) = pT * D.ρT x * iT) ∧ ∀ x, D'.ρM (π x) = pM * D.ρM x * iM := by
  atlas_forward_decl GlobalTheory.DetInv.datum_idempotent_part
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PartShift

section Abstract

variable {O : Type} [CommRing O] {K : Type} [CommRing K] [Algebra O K]
  {Γ Λ : Type} [CommRing Γ] [CommRing Λ] {h h' : ℕ}
  {ρ : Γ → Matrix (Fin h) (Fin h) O} {ρ' : Λ → Matrix (Fin h') (Fin h') O}
  {π : Γ →+* Λ} {e : Γ} {P : Matrix (Fin h') (Fin h) O} {I : Matrix (Fin h) (Fin h') O}

theorem mulVec_mem_eigenspace (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (he : π e = 1) (σ : Λ →+* O) (v : Fin h → K)
    (hv : ∀ a, (ρ a).map (algebraMap O K) *ᵥ v = algebraMap O K (σ (π a)) • v) (a : Λ) :
    (ρ' a).map (algebraMap O K) *ᵥ (P.map (algebraMap O K) *ᵥ v) =
      algebraMap O K (σ a) • (P.map (algebraMap O K) *ᵥ v) := by
  obtain ⟨x, rfl⟩ := hπ a
  have hIPk : I.map (algebraMap O K) * P.map (algebraMap O K) = (ρ e).map (algebraMap O K) := by
    rw [← Matrix.map_mul, hIP]
  have hev : (ρ e).map (algebraMap O K) *ᵥ v = v := by rw [hv, he, map_one, map_one, one_smul]
  calc (ρ' (π x)).map (algebraMap O K) *ᵥ (P.map (algebraMap O K) *ᵥ v)
      = P.map (algebraMap O K) *ᵥ ((ρ x).map (algebraMap O K) *ᵥ
          ((I.map (algebraMap O K) * P.map (algebraMap O K)) *ᵥ v)) := by
        rw [hact]; simp only [Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [hIPk, hev, hv, Matrix.mulVec_smul]

theorem mulVec_mulVec_eq_self_of_eigenvector (hIP : I * P = ρ e) (he : π e = 1) (σ : Λ →+* O) (v : Fin h → K)
    (hv : ∀ a, (ρ a).map (algebraMap O K) *ᵥ v = algebraMap O K (σ (π a)) • v) :
    I.map (algebraMap O K) *ᵥ (P.map (algebraMap O K) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hIP, hv, he, map_one, map_one, one_smul]

theorem I_eigen (hPI : P * I = 1) (hIP : I * P = ρ e)
    (hcomm : ∀ x, ρ x * ρ e = ρ e * ρ x) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (τ : Λ →+* O) (w : Fin h' → K)
    (hw : ∀ a, (ρ' a).map (algebraMap O K) *ᵥ w = algebraMap O K (τ a) • w) (x : Γ) :
    (ρ x).map (algebraMap O K) *ᵥ (I.map (algebraMap O K) *ᵥ w) =
      algebraMap O K (τ (π x)) • (I.map (algebraMap O K) *ᵥ w) := by
  have key : ρ x * I = I * (P * ρ x * I) := by
    calc ρ x * I = ρ x * (I * P * I) := by rw [Matrix.mul_assoc, hPI, Matrix.mul_one]
      _ = (ρ x * ρ e) * I := by rw [hIP, Matrix.mul_assoc]
      _ = (ρ e * ρ x) * I := by rw [hcomm]
      _ = I * (P * ρ x * I) := by rw [← hIP]; simp only [Matrix.mul_assoc]
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, key, ← hact, Matrix.map_mul, ← Matrix.mulVec_mulVec,
    hw, Matrix.mulVec_smul]

end Abstract

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

section EigC

variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Γ Λ : Type} [CommRing Γ] [CommRing Λ] {h h' : ℕ}
  {ρ : Γ → Matrix (Fin h) (Fin h) O} {ρ' : Λ → Matrix (Fin h') (Fin h') O}
  {π : Γ →+* Λ} {e : Γ} {P : Matrix (Fin h') (Fin h) O} {I : Matrix (Fin h) (Fin h') O}

theorem mem_eig_iff {n : ℕ} {Δ : Type} [CommRing Δ] (ρ₀ : Δ → Matrix (Fin n) (Fin n) O)
    (σ : Δ →+* O) (v : Fin n → C) :
    v ∈ eig C ρ₀ σ ↔ ∀ a, (ρ₀ a).map (algebraMap O C) *ᵥ v = algebraMap O C (σ a) • v := by
  simp [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem eig_P (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (he : π e = 1) (σ : Λ →+* O) {v : Fin h → C}
    (hv : v ∈ eig C ρ (σ.comp π)) : Matrix.toLin' (P.map (algebraMap O C)) v ∈ eig C ρ' σ := by
  rw [mem_eig_iff] at hv ⊢
  intro a
  rw [Matrix.toLin'_apply]
  exact mulVec_mem_eigenspace hIP hact hπ he σ v (fun a => hv a) a

theorem eig_IP (hIP : I * P = ρ e) (he : π e = 1) (σ : Λ →+* O) {v : Fin h → C}
    (hv : v ∈ eig C ρ (σ.comp π)) :
    Matrix.toLin' (I.map (algebraMap O C)) (Matrix.toLin' (P.map (algebraMap O C)) v) = v := by
  rw [mem_eig_iff] at hv
  simp only [Matrix.toLin'_apply]
  exact mulVec_mulVec_eq_self_of_eigenvector hIP he σ v (fun a => hv a)

theorem eig_I (hPI : P * I = 1) (hIP : I * P = ρ e)
    (hcomm : ∀ x, ρ x * ρ e = ρ e * ρ x) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (τ : Λ →+* O) {w : Fin h' → C} (hw : w ∈ eig C ρ' τ) :
    Matrix.toLin' (I.map (algebraMap O C)) w ∈ eig C ρ (τ.comp π) := by
  rw [mem_eig_iff] at hw ⊢
  intro x
  rw [Matrix.toLin'_apply]
  exact I_eigen hPI hIP hcomm hact τ w hw x

theorem eig_PI (hPI : P * I = 1) (w : Fin h' → C) :
    Matrix.toLin' (P.map (algebraMap O C)) (Matrix.toLin' (I.map (algebraMap O C)) w) = w := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hPI,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

theorem eq_zero_or_factors_of_mem_eigenspace (hPI : P * I = 1) (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {1 - e})
    (hinj : Function.Injective (algebraMap O C)) (he2 : IsIdempotentElem e)
    (σ : Γ →+* O) {v : Fin h → C} (hv : v ∈ eig C ρ σ) :
    Matrix.toLin' (P.map (algebraMap O C)) v = 0 ∨ ∃ σ' : Λ →+* O, σ = σ'.comp π := by
  have hidem : IsIdempotentElem (algebraMap O C (σ e)) := by
    unfold IsIdempotentElem; rw [← map_mul, ← map_mul, he2.eq]
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hidem) with h0 | h1
  · left
    rw [mem_eig_iff] at hv
    have hP : P = P * ρ e := by rw [← hIP, ← Matrix.mul_assoc, hPI, Matrix.one_mul]
    rw [Matrix.toLin'_apply, hP, Matrix.map_mul, ← Matrix.mulVec_mulVec, hv, h0, zero_smul,
      Matrix.mulVec_zero]
  · right
    have hσe : σ e = 1 := hinj (by rw [h1, map_one])
    have hle : RingHom.ker π ≤ RingHom.ker σ := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff]
      simp [RingHom.mem_ker, map_sub, hσe]
    refine ⟨π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨σ, hle⟩,
      ?_⟩
    exact (RingHom.liftOfRightInverse_comp π _ _ ⟨σ, hle⟩).symm

end EigC

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

section Part

variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Γ Λ : Type} [CommRing Γ] [CommRing Λ] {h h' : ℕ}
  {ρ : Γ → Matrix (Fin h) (Fin h) O} {ρ' : Λ → Matrix (Fin h') (Fin h') O}
  {π : Γ →+* Λ} {e : Γ} {P : Matrix (Fin h') (Fin h) O} {I : Matrix (Fin h) (Fin h') O}

theorem pi_e (hker : RingHom.ker π = Ideal.span {1 - e}) : π e = 1 := by
  have : (1 - e) ∈ RingHom.ker π := hker ▸ Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
  exact this.symm

theorem toLin_incl {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) (t : Fin n → O) :
    Matrix.toLin' (X.map (algebraMap O C)) (incl C n t) = incl C m (X *ᵥ t) := by
  funext i
  rw [Matrix.toLin'_apply]
  exact (RingHom.map_mulVec (algebraMap O C) X t i).symm

theorem sup_P (hPI : P * I = 1) (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {1 - e})
    (hinj : Function.Injective (algebraMap O C)) (he2 : IsIdempotentElem e) (τ : Λ →+* O)
    {s : Fin h → C} (hs : s ∈ ⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1) :
    Matrix.toLin' (P.map (algebraMap O C)) s ∈ ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1 := by
  have : (⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1) ≤
      (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1).comap
        (Matrix.toLin' (P.map (algebraMap O C))) := by
    refine iSup_le ?_
    rintro ⟨σ, hσ⟩ v hv
    rw [Submodule.mem_comap]
    rcases eq_zero_or_factors_of_mem_eigenspace C hPI hIP hact hπ hker hinj he2 σ hv with h0 | ⟨σ', rfl⟩
    · rw [h0]; exact Submodule.zero_mem _
    · have hne : σ' ≠ τ := fun hh => hσ (by rw [hh])
      exact Submodule.mem_iSup_of_mem (⟨σ', hne⟩ : {σ : Λ →+* O // σ ≠ τ})
        (eig_P C hIP hact hπ (pi_e hker) σ' hv)
  exact this hs

theorem sup_I (hPI : P * I = 1) (hIP : I * P = ρ e)
    (hcomm : ∀ x, ρ x * ρ e = ρ e * ρ x) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (τ : Λ →+* O)
    {s : Fin h' → C} (hs : s ∈ ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1) :
    Matrix.toLin' (I.map (algebraMap O C)) s ∈
      ⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1 := by
  have : (⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ' σ.1) ≤
      (⨆ σ : {σ : Γ →+* O // σ ≠ τ.comp π}, eig C ρ σ.1).comap
        (Matrix.toLin' (I.map (algebraMap O C))) := by
    refine iSup_le ?_
    rintro ⟨σ, hσ⟩ v hv
    rw [Submodule.mem_comap]
    have hne : σ.comp π ≠ τ.comp π := by
      intro hh
      refine hσ (RingHom.ext fun a => ?_)
      obtain ⟨x, rfl⟩ := hπ a
      exact RingHom.congr_fun hh x
    exact Submodule.mem_iSup_of_mem (⟨σ.comp π, hne⟩ : {σ : Γ →+* O // σ ≠ τ.comp π})
      (eig_I C hPI hIP hcomm hact σ hv)
  exact this hs

theorem eigPart_P (hPI : P * I = 1) (hIP : I * P = ρ e) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = Ideal.span {1 - e})
    (hinj : Function.Injective (algebraMap O C)) (he2 : IsIdempotentElem e) (τ : Λ →+* O)
    {L : Submodule O (Fin h → O)} {L' : Submodule O (Fin h' → O)} (hL : ∀ t ∈ L, P *ᵥ t ∈ L')
    {y : Fin h → C} (hy : y ∈ eigPart C ρ (τ.comp π) L) :
    Matrix.toLin' (P.map (algebraMap O C)) y ∈ eigPart C ρ' τ L' := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨eig_P C hIP hact hπ (pi_e hker) τ h1, ?_⟩
  obtain ⟨a, ⟨t, ht, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 h2
  rw [map_add, toLin_incl]
  exact Submodule.add_mem_sup ⟨_, hL t ht, rfl⟩ (sup_P C hPI hIP hact hπ hker hinj he2 τ hb)

theorem eigPart_I (hPI : P * I = 1) (hIP : I * P = ρ e)
    (hcomm : ∀ x, ρ x * ρ e = ρ e * ρ x) (hact : ∀ x, ρ' (π x) = P * ρ x * I)
    (hπ : Function.Surjective π) (τ : Λ →+* O)
    {L : Submodule O (Fin h → O)} {L' : Submodule O (Fin h' → O)} (hL : ∀ t ∈ L', I *ᵥ t ∈ L)
    {y : Fin h' → C} (hy : y ∈ eigPart C ρ' τ L') :
    Matrix.toLin' (I.map (algebraMap O C)) y ∈ eigPart C ρ (τ.comp π) L := by
  obtain ⟨h1, h2⟩ := hy
  refine ⟨eig_I C hPI hIP hcomm hact τ h1, ?_⟩
  obtain ⟨a, ⟨t, ht, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 h2
  rw [map_add, toLin_incl]
  exact Submodule.add_mem_sup ⟨_, hL t ht, rfl⟩ (sup_I C hPI hIP hcomm hact hπ τ hb)

theorem basis_transport (f : (Fin h → C) →ₗ[C] (Fin h' → C)) (g : (Fin h' → C) →ₗ[C] (Fin h → C))
    {S : Submodule O (Fin h → C)} {S' : Submodule O (Fin h' → C)}
    (h1 : ∀ x ∈ S, f x ∈ S' ∧ g (f x) = x) (h2 : ∀ y ∈ S', ∃ x ∈ S, f x = y)
    {n : ℕ} {x : Fin n → Fin h → C} (hx : IsBasisOf C S x) :
    IsBasisOf C S' (fun i => f (x i)) := by
  obtain ⟨hli, hsp⟩ := hx
  have hmem : ∀ i, x i ∈ S := fun i => hsp ▸ Submodule.subset_span ⟨i, rfl⟩
  constructor
  · refine LinearIndependent.of_comp g ?_
    have : (⇑g ∘ fun i => f (x i)) = x := funext fun i => (h1 _ (hmem i)).2
    rw [this]; exact hli
  · have : (Set.range fun i => f (x i)) = (f.restrictScalars O) '' Set.range x := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hsp]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (h1 y hy).1
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := h2 y hy
      exact ⟨z, hz, rfl⟩

theorem finrank_eq_of_inverse {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    {S : Submodule R M} {S' : Submodule R N}
    (h1 : ∀ x ∈ S, f x ∈ S' ∧ g (f x) = x) (h2 : ∀ y ∈ S', g y ∈ S ∧ f (g y) = y) :
    Module.finrank R S' = Module.finrank R S := by
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear (g.restrict fun y hy => (h2 y hy).1)
    (f.restrict fun x hx => (h1 x hx).1) ?_ ?_)
  · ext x : 2
    exact (h1 x.1 x.2).2
  · ext y : 2
    exact (h2 y.1 y.2).2

end Part

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv.PartShift

section Data

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

theorem mem_Tsub_iff (D : Datum ε h Λ) (σ : Λ →+* O) (t : Fin h → O) :
    t ∈ D.Tsub σ ↔ ∀ a, (actT D a).map (algebraMap O O) *ᵥ t = algebraMap O O (σ a) • t := by
  simp [Datum.Tsub, actT, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem map_ofPadic_theta {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℤ_[p]) :
    (X.map (ofPadic p O)).map (WittVector.fontaineTheta O p) = X.map (padicToO p O) := rfl

end Data

end GlobalTheory.DetInv.PartShift

namespace GlobalTheory.DetInv

open PartShift

theorem part_rank_dim_shift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Γ : Type) [CommRing Γ] [Algebra ℤ_[p] Γ] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (π : Γ →ₐ[ℤ_[p]] Λ) (e : Γ), IsIdempotentElem e → Function.Surjective π → RingHom.ker π = Ideal.span {1 - e} → ∀ (h h' : ℕ) (D : Datum ε h Γ) (D' : Datum ε h' Λ) (iT : Matrix (Fin h) (Fin h') ℤ_[p]) (pT : Matrix (Fin h') (Fin h) ℤ_[p]) (iM : Matrix (Fin h) (Fin h') (Ainf p O)) (pM : Matrix (Fin h') (Fin h) (Ainf p O)), (pT * iT = 1 ∧ iT * pT = D.ρT e ∧ pM * iM = 1 ∧ iM * pM = D.ρM e ∧ D'.F = pM * D.F * iT.map (ofPadic p O) ∧ D'.G = pT.map (ofPadic p O) * D.G * iM ∧ (∀ x, D'.ρT (π x) = pT * D.ρT x * iT) ∧ ∀ x, D'.ρM (π x) = pM * D.ρM x * iM) → (⨆ σ : Γ →+* O, eig C (actT D) σ) = ⊤ → (⨆ σ : Γ →+* O, eig C (actH D) σ) = ⊤ → ∀ τ : Λ →+* O, D'.lieRank τ = D.lieRank (τ.comp (π : Γ →+* Λ)) ∧ Module.finrank C (eig C (actT D') τ) = Module.finrank C (eig C (actT D) (τ.comp (π : Γ →+* Λ))) ∧ ∀ r, IsShift C v D' τ r → IsShift C v D (τ.comp (π : Γ →+* Λ)) r := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Γ _ _ Λ _ _ π e he2 hπ hker h h' D D' iT pT iM pM
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ _ _ τ
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  obtain ⟨-, -, hG, -, -⟩ := datum_scalar_intertwine p C v O hv ε hε Γ h D
  obtain ⟨π₀, hπ₀⟩ : ∃ π₀ : Γ →+* Λ, π₀ = (π : Γ →+* Λ) := ⟨_, rfl⟩
  have hππ : ∀ x, π x = π₀ x := fun x => by rw [hπ₀]; rfl
  have hπ' : Function.Surjective π₀ := by rw [hπ₀]; exact hπ
  have hker' : RingHom.ker π₀ = Ideal.span {1 - e} := by rw [hπ₀]; exact hker
  rw [← hπ₀]
  have he : π₀ e = 1 := pi_e hker'
  obtain ⟨P, hP⟩ : ∃ P, P = pT.map (padicToO p O) := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = iT.map (padicToO p O) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = pM.map (WittVector.fontaineTheta O p) := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = iM.map (WittVector.fontaineTheta O p) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = D.F.map (WittVector.fontaineTheta O p) := ⟨_, rfl⟩
  obtain ⟨G, hG0⟩ : ∃ G, G = D.G.map (WittVector.fontaineTheta O p) := ⟨_, rfl⟩
  have hPI : P * I = 1 := by
    rw [hP, hI, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hIP : I * P = actT D e := by rw [hP, hI, ← Matrix.map_mul, h2]; rfl
  have hQJ : Q * J = 1 := by
    rw [hQ, hJ, ← Matrix.map_mul, h3, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJQ : J * Q = actH D e := by rw [hQ, hJ, ← Matrix.map_mul, h4]; rfl
  have hcT : ∀ x, actT D x * actT D e = actT D e * actT D x := fun x => by
    simp only [actT, ← Matrix.map_mul, ← map_mul, mul_comm x e]
  have hcH : ∀ x, actH D x * actH D e = actH D e * actH D x := fun x => by
    simp only [actH, ← Matrix.map_mul, ← map_mul, mul_comm x e]
  have haT : ∀ x, actT D' (π₀ x) = P * actT D x * I := fun x => by
    rw [← hππ, actT, h7, Matrix.map_mul, Matrix.map_mul, hP, hI]; rfl
  have haH : ∀ x, actH D' (π₀ x) = Q * actH D x * J := fun x => by
    rw [← hππ, actH, h8, Matrix.map_mul, Matrix.map_mul, hQ, hJ]; rfl
  have hF' : D'.F.map (WittVector.fontaineTheta O p) = Q * F * I := by
    rw [h5, Matrix.map_mul, Matrix.map_mul, map_ofPadic_theta, hQ, hF, hI]
  have hG' : D'.G.map (WittVector.fontaineTheta O p) = P * G * J := by
    rw [h6, Matrix.map_mul, Matrix.map_mul, map_ofPadic_theta, hP, hG0, hJ]
  have hFe : F * (I * P) = J * Q * F := by
    rw [hIP, hJQ, hF, actT, actH, ← map_ofPadic_theta, ← Matrix.map_mul, D.F_act, Matrix.map_mul]
  have hGe : G * (J * Q) = I * P * G := by
    rw [hIP, hJQ, hG0, actT, actH, ← map_ofPadic_theta, ← Matrix.map_mul, hG, Matrix.map_mul]
  have g1 : P * G * J * Q = P * G := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hGe, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPI,
      Matrix.one_mul]
  have g2 : I * (P * G * J) = G * J := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hGe, Matrix.mul_assoc, Matrix.mul_assoc, hQJ,
      Matrix.mul_one]
  have f1 : Q * F * I * P = Q * F := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hFe, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQJ,
      Matrix.one_mul]
  have f2 : J * (Q * F * I) = F * I := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hFe, Matrix.mul_assoc, Matrix.mul_assoc, hPI,
      Matrix.mul_one]
  have hbb : ∀ t, D.bb t = G *ᵥ t := fun t => by rw [hG0]; rfl
  have hbb' : ∀ t, D'.bb t = (P * G * J) *ᵥ t := fun t => by rw [← hG']; rfl
  have hal : ∀ w, alC C D w = F.map (algebraMap O C) *ᵥ w := fun t => by rw [hF]; rfl
  have hal' : ∀ w, alC C D' w = (Q * F * I).map (algebraMap O C) *ᵥ w := fun t => by
    rw [← hF']; rfl

  have lie1 : ∀ u ∈ D.Lie ⊓ D.Tsub (τ.comp π₀),
      P *ᵥ u ∈ D'.Lie ⊓ D'.Tsub τ ∧ I *ᵥ (P *ᵥ u) = u := by
    rintro u ⟨⟨y, hy⟩, hu⟩
    have hu' := (mem_Tsub_iff D _ u).1 hu
    refine ⟨⟨⟨Q *ᵥ y, ?_⟩, (mem_Tsub_iff D' _ _).2 fun a => ?_⟩, ?_⟩
    · rw [← hy, hbb, hbb', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, g1]
    · simpa using mulVec_mem_eigenspace hIP haT hπ' he τ u hu' a
    · simpa using mulVec_mulVec_eq_self_of_eigenvector hIP he τ u hu'
  have lie2 : ∀ u ∈ D'.Lie ⊓ D'.Tsub τ,
      I *ᵥ u ∈ D.Lie ⊓ D.Tsub (τ.comp π₀) ∧ P *ᵥ (I *ᵥ u) = u := by
    rintro u ⟨⟨y, hy⟩, hu⟩
    have hu' := (mem_Tsub_iff D' _ u).1 hu
    refine ⟨⟨⟨J *ᵥ y, ?_⟩, (mem_Tsub_iff D _ _).2 fun a => ?_⟩, ?_⟩
    · rw [← hy, hbb, hbb', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, g2]
    · simpa using I_eigen hPI hIP hcT haT τ u hu' a
    · rw [Matrix.mulVec_mulVec, hPI, Matrix.one_mulVec]
  refine ⟨finrank_eq_of_inverse (Matrix.toLin' P) (Matrix.toLin' I) lie1 lie2,
    finrank_eq_of_inverse (Matrix.toLin' (P.map (algebraMap O C)))
      (Matrix.toLin' (I.map (algebraMap O C)))
      (fun x hx => ⟨eig_P C hIP haT hπ' he τ hx, eig_IP C hIP he τ hx⟩)
      (fun y hy => ⟨eig_I C hPI hIP hcT haT τ hy, eig_PI C hPI y⟩), ?_⟩
  intro r hr a b x g m k hx hg hm hk
  have tP : ∀ y ∈ eigPart C (actT D) (τ.comp π₀) ⊤,
      Matrix.toLin' (P.map (algebraMap O C)) y ∈ eigPart C (actT D') τ ⊤ := fun y hy =>
    eigPart_P C hPI hIP haT hπ' hker' hinj he2 τ (fun _ _ => Submodule.mem_top) hy
  have tI : ∀ y ∈ eigPart C (actT D') τ ⊤,
      Matrix.toLin' (I.map (algebraMap O C)) y ∈ eigPart C (actT D) (τ.comp π₀) ⊤ := fun y hy =>
    eigPart_I C hPI hIP hcT haT hπ' τ (fun _ _ => Submodule.mem_top) hy
  have a1 : ∀ w, alC C D' (Matrix.toLin' (P.map (algebraMap O C)) w) =
      Matrix.toLin' (Q.map (algebraMap O C)) (alC C D w) := fun w => by
    rw [hal, hal', Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, f1]
  have a2 : ∀ w, alC C D (Matrix.toLin' (I.map (algebraMap O C)) w) =
      Matrix.toLin' (J.map (algebraMap O C)) (alC C D' w) := fun w => by
    rw [hal, hal', Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, f2]
  refine hr a b (fun i => Matrix.toLin' (P.map (algebraMap O C)) (x i)) g
    (fun i => Matrix.toLin' (Q.map (algebraMap O C)) (m i)) k ?_ ?_ ?_ ?_
  · refine basis_transport C _ (Matrix.toLin' (I.map (algebraMap O C))) ?_ ?_ hx
    · rintro _ ⟨u, hu, rfl⟩
      rw [toLin_incl, toLin_incl, (lie1 u hu).2]
      exact ⟨⟨_, (lie1 u hu).1, rfl⟩, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨_, ⟨_, (lie2 u hu).1, rfl⟩, by rw [toLin_incl, (lie2 u hu).2]⟩
  · have := basis_transport C (Matrix.toLin' (P.map (algebraMap O C)))
      (Matrix.toLin' (I.map (algebraMap O C))) (S' := wQuot C D' τ) ?_ ?_ hg
    · simpa only [map_sum, map_smul] using this
    · rintro y ⟨hy, hy0⟩
      refine ⟨⟨tP y hy, ?_⟩, eig_IP C hIP he τ hy.1⟩
      have hy1 : alC C D y = 0 := hy0
      show alC C D' _ = 0
      rw [a1, hy1, map_zero]
    · rintro y ⟨hy, hy0⟩
      refine ⟨_, ⟨tI y hy, ?_⟩, eig_PI C hPI y⟩
      have hy1 : alC C D' y = 0 := hy0
      show alC C D _ = 0
      rw [a2, hy1, map_zero]
  · refine basis_transport C _ (Matrix.toLin' (J.map (algebraMap O C))) ?_ ?_ hm
    · intro y hy
      refine ⟨eigPart_P C hQJ hJQ haH hπ' hker' hinj he2 τ (fun t ht => ?_) hy,
        eig_IP C hJQ he τ hy.1⟩
      have ht1 : D.bb t = 0 := ht
      show D'.bb _ = 0
      rw [hbb] at ht1
      rw [hbb', Matrix.mulVec_mulVec, g1, ← Matrix.mulVec_mulVec, ht1, Matrix.mulVec_zero]
    · intro y hy
      refine ⟨_, eigPart_I C hQJ hJQ hcH haH hπ' τ (fun t ht => ?_) hy, eig_PI C hQJ y⟩
      have ht1 : D'.bb t = 0 := ht
      show D.bb _ = 0
      rw [hbb'] at ht1
      rw [hbb, Matrix.mulVec_mulVec, ← g2, ← Matrix.mulVec_mulVec, ht1, Matrix.mulVec_zero]
  · have := basis_transport C (Matrix.toLin' (Q.map (algebraMap O C)))
      (Matrix.toLin' (J.map (algebraMap O C))) (S' := alQuot C D' τ) ?_ ?_ hk
    · simpa only [map_sum, map_smul] using this
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨⟨_, tP w hw, a1 w⟩, ?_⟩
      show Matrix.toLin' _ (Matrix.toLin' _ (alC C D w)) = alC C D w
      rw [← a1, ← a2, eig_IP C hIP he τ hw.1]
    · rintro _ ⟨w, hw, rfl⟩
      refine ⟨_, ⟨_, tI w hw, rfl⟩, ?_⟩
      show Matrix.toLin' _ (alC C D _) = alC C D' w
      rw [← a1, eig_PI C hPI]

end GlobalTheory.DetInv
end

section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pdiv_group_for_point : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.tateGt) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (c t) = pairT P.A P.eps (e s : P.T) t • ζ) ∧ ∀ x t, l x (dlog (G := G) (c t)) = (P.al₀ t).1 x := by
  first | exact @GlobalTheory.RaynaudPDiv.exists_pDivGroup_raynaud | exact GlobalTheory.RaynaudPDiv.exists_pDivGroup_raynaud | (intros; apply GlobalTheory.RaynaudPDiv.exists_pDivGroup_raynaud <;> assumption)
end

section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_pairing_sandwich : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (G : PDivGroup p O) (ζ : (PDivGroup.mu p O).Tate) (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]), v.Integers O → Function.Bijective (fun a : ℤ_[p] => a • ζ) → (∀ s χ, pairing G O s χ = B s χ • ζ) → (∀ x : O ⊗[ℤ_[p]] G.Tate, G.hodgeTateLinear x = 0 ↔ ∃ (c : O) (y : G.Lie), c ≠ 0 ∧ ∀ χ, c * (TensorProduct.rid ℤ_[p] O) ((B.flip χ).baseChange O x) = y (dlog (G := G) χ)) ∧ Module.finrank O (LinearMap.ker G.hodgeTateLinear) + Module.finrank O (LinearMap.ker G.dual.hodgeTateLinear) = G.height := by
  first | exact @GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear | exact GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear | (intros; apply GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear <;> assumption)
end

section
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PointGroup

theorem exists_retraction {p : ℕ} [Fact p.Prime] {M M' : Type} [CommGroup M] [CommGroup M']
    (f : M →* M') (hf : Function.Injective f) [Module.Finite ℤ_[p] (HTLat.Tate p M')] :
    ∃ r : HTLat.Tate p M' →ₗ[ℤ_[p]] LinearMap.range (HTLat.Tate.map p f),
      ∀ s : LinearMap.range (HTLat.Tate.map p f), r s = s := by
  set S := LinearMap.range (HTLat.Tate.map p f)
  have h1 : ∀ t, (p : ℤ_[p]) • t ∈ S → t ∈ S := by
    rintro t ⟨u, hu⟩
    have h : ∀ n, f (u.lev (n + 1)) = t.lev n := fun n => by
      rw [← HTLat.Tate.lev_map, hu, HTLat.Tate.lev_smul, PDiv.pow_digit_natCast (t.lev_pow _),
        t.lev_succ]
    exact ⟨HTLat.Tate.mk (fun n => u.lev (n + 1)) fun n =>
      ⟨hf (by rw [map_pow, h, t.lev_pow, map_one]), u.lev_succ _⟩, HTLat.Tate.ext h⟩
  have h2 : ∀ (n : ℕ) t, (p : ℤ_[p]) ^ n • t ∈ S → t ∈ S := fun n => by
    induction n with
    | zero => simp
    | succ n ih => exact fun t ht => h1 t (ih _ (by rwa [smul_smul, ← pow_succ]))
  haveI : Module.IsTorsionFree ℤ_[p] (HTLat.Tate p M' ⧸ S) := .of_smul_eq_zero fun a q h => by
    by_cases ha : a = 0
    · exact .inl ha
    obtain ⟨t, rfl⟩ := S.mkQ_surjective q
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      PadicInt.unitCoeff_spec ha, mul_smul] at h
    exact .inr ((Submodule.Quotient.mk_eq_zero _).2 (h2 _ t ((S.smul_mem_iff' (PadicInt.unitCoeff ha)).1 h)))
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property S.mkQ LinearMap.id S.mkQ_surjective
  refine ⟨(LinearMap.id - σ ∘ₗ S.mkQ).codRestrict S fun t => ?_, fun s => Subtype.ext ?_⟩
  · change s.1 - σ (S.mkQ s.1) = s.1
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 s.2, map_zero, sub_zero]
  · rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, LinearMap.sub_apply, map_sub]
    exact sub_eq_zero.2 (LinearMap.congr_fun hσ (S.mkQ t)).symm

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O]
  [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ]
  (P : Point p v O Λ)

theorem pairV_inclT (x z : O ⊗[ℤ_[p]] P.T) : P.pairV (P.inclT x) (P.inclT z) =
    algebraMap O C (LinearMap.BilinForm.baseChange O (pairT P.A P.eps) x z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul c s =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul d t =>
      rw [P.inclT_tmul, P.inclT_tmul, P.pairV_tmul, LinearMap.BilinForm.baseChange_tmul,
        Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, ← IsScalarTower.algebraMap_apply]

theorem inclT_injective : Function.Injective P.inclT := by
  have h : ∀ x, P.inclT x = ((Algebra.linearMap O C).restrictScalars ℤ_[p]).rTensor P.T x :=
    fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul c s => rw [P.inclT_tmul]; rfl
  intro x y hxy
  rw [h, h] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap _ P.integers.hom_inj hxy

omit [IsAlgClosed C] [CharZero C] in
theorem inclT_baseChange (g : P.T →ₗ[ℤ_[p]] P.T) (x : O ⊗[ℤ_[p]] P.T) :
    P.inclT (g.baseChange O x) = g.baseChange C (P.inclT x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c s => rw [LinearMap.baseChange_tmul, P.inclT_tmul, P.inclT_tmul, LinearMap.baseChange_tmul]

theorem pairT_flip_bijective : Function.Bijective (pairT P.A P.eps).flip := by
  have h : (pairT P.A P.eps).flip = -pairT P.A P.eps :=
    LinearMap.ext₂ fun s t => ((isAlt_pairT P.A P.eps).neg_eq s t).symm
  rw [h]
  exact neg_bijective.comp P.pairT_bijective

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem mem_W_of_smul {c : O} (hc : c ≠ 0) {w : P.V} (h : c • w ∈ P.W) : w ∈ P.W := by
  rw [← algebraMap_smul C c] at h
  exact (P.W.smul_mem_iff ((map_ne_zero_iff _ P.integers.hom_inj).2 hc)).1 h

theorem inclT_mem_W_iff (K : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P) (z : O ⊗[ℤ_[p]] P.T) :
    P.inclT z ∈ P.W ↔ ∀ x, P.inclT x ∈ P.W →
      LinearMap.BilinForm.baseChange O (pairT P.A P.eps) x z = 0 := by
  have h5 := K.2.2.2.2.1
  refine ⟨fun hz x hx => P.integers.hom_inj ?_, fun h => (h5 _).2 fun y hy => ?_⟩
  · rw [← pairV_inclT, map_zero]
    exact (h5 _).1 hx _ hz
  · obtain ⟨a, ha, x, hx⟩ := P.exists_smul_mem_latT y
    have h1 := pairV_inclT P x z
    rw [h x (by rw [hx, ← algebraMap_smul C a]; exact P.W.smul_mem _ hy), map_zero, hx,
      ← algebraMap_smul C a, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    rw [P.pairV_swap, (mul_eq_zero.1 h1).resolve_left ((map_ne_zero_iff _ P.integers.hom_inj).2 ha),
      neg_zero]

theorem mem_W_iff [IsDomain O] (K : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P) (w : P.V) :
    w ∈ P.W ↔ ∃ c : O, c ≠ 0 ∧ c • w ∈ P.latLie := by
  constructor
  · rw [K.2.2.2.2.2.2]
    intro hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hx⟩ := hx
      obtain ⟨b, hb, hy⟩ := hy
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul d x _ hx =>
      obtain ⟨a, ha, hx⟩ := hx
      haveI := P.integers.isFractionRing
      obtain ⟨⟨n, b⟩, hb⟩ := IsLocalization.surj (nonZeroDivisors O) d
      refine ⟨a * b, mul_ne_zero ha (nonZeroDivisors.ne_zero b.2), ?_⟩
      rw [mul_smul, ← algebraMap_smul C (b : O), smul_smul _ d, mul_comm _ d, hb, algebraMap_smul,
        smul_comm]
      exact Submodule.smul_mem _ _ hx
  · rintro ⟨c, hc, z, hz⟩
    refine mem_W_of_smul P hc ?_
    rw [← hz, K.2.2.2.2.2.2]
    exact Submodule.subset_span ⟨z, rfl⟩

theorem ker_iff_of_weil [IsDomain O] (K : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P) {G : PDivGroup p O}
    (j : G.Tate →ₗ[ℤ_[p]] P.T) (r : P.T →ₗ[ℤ_[p]] G.Tate) (hr : ∀ s, r (j s) = s)
    (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (c : P.T →ₗ[ℤ_[p]] G.dual.Tate)
    (B : G.Tate →ₗ[ℤ_[p]] G.dual.Tate →ₗ[ℤ_[p]] ℤ_[p]) (hB : Function.Injective B.flip)
    (hk : KerIsLie G B) (hc : ∀ s t, B s (c t) = pairT P.A P.eps (j s) t)
    (hl : ∀ x t, l x (dlog G (c t)) = (P.al₀ t).1 x) (x : O ⊗[ℤ_[p]] G.Tate) :
    G.hodgeTateLinear x = 0 ↔ P.inclT (j.baseChange O x) ∈ P.W := by
  have h1 : Function.Surjective c := fun χ => by
    obtain ⟨t, ht⟩ := (pairT_flip_bijective P).2 (B.flip χ ∘ₗ r)
    refine ⟨t, hB (LinearMap.ext fun s => (hc s t).trans ?_)⟩
    exact (LinearMap.congr_fun ht (j s)).trans (by rw [LinearMap.comp_apply, hr])
  have h2 : ∀ t, P.pairV (P.inclT (j.baseChange O x)) (1 ⊗ₜ t) =
      algebraMap O C (TensorProduct.rid ℤ_[p] O ((B.flip (c t)).baseChange O x)) := fun t => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul a s =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, P.inclT_tmul, P.pairV_tmul,
        LinearMap.flip_apply, hc, TensorProduct.rid_tmul, mul_one, Algebra.smul_def,
        Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
  have h3 : ∀ (a : O) t, P.pairV (a • P.inclT (j.baseChange O x)) (1 ⊗ₜ t) =
      algebraMap O C (a * TensorProduct.rid ℤ_[p] O ((B.flip (c t)).baseChange O x)) := fun a t => by
    rw [← algebraMap_smul C a, map_smul, LinearMap.smul_apply, h2, smul_eq_mul, map_mul]
  rw [hk x, mem_W_iff P K]
  constructor
  · rintro ⟨a, y, ha, h⟩
    obtain ⟨z, rfl⟩ := l.surjective y
    exact ⟨a, ha, z, P.eq_of_pairV fun t => by rw [h3, h, hl, P.pairV_bLie]⟩
  · rintro ⟨a, ha, z, hz⟩
    refine ⟨a, l z, ha, fun χ => ?_⟩
    obtain ⟨t, rfl⟩ := h1 χ
    exact P.integers.hom_inj (by rw [← h3, ← hz, hl, P.pairV_bLie])

theorem exists_group (SW : GlobalTheory.Published.ScholzeWeinsteinB) :
    ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.T), ∀ x, G.hodgeTateLinear x = 0 ↔
      P.inclT (e.toLinearMap.baseChange O x) ∈ P.W := by
  obtain ⟨b⟩ := P.nonempty_T_equiv
  obtain ⟨G, e, h⟩ := (SW p C v O P.integers).2 _
    ((P.W.restrictScalars O).comap (P.inclT ∘ₗ b.symm.toLinearMap.baseChange O))
    fun c x hc hx => mem_W_of_smul P hc (by rw [← map_smul]; exact hx)
  refine ⟨G, e.trans b.symm, fun x => (h x).trans ?_⟩
  rw [LinearEquiv.coe_trans, LinearMap.baseChange_comp]
  rfl

theorem exists_retraction_tateGt :
    ∃ r : P.T →ₗ[ℤ_[p]] P.tateGt, ∀ s : P.tateGt, r s = s := by
  have h : Module.Finite ℤ_[p] P.T := inferInstance
  unfold Point.tateGt
  exact @exists_retraction p _ _ _ (_) (_) _ P.toA_injective h

omit [IsAlgClosed C] [CharZero C] in
theorem baseChange_eq_self {T : Type} [AddCommGroup T] [Module ℤ_[p] T] (S : Submodule ℤ_[p] T)
    (g : T →ₗ[ℤ_[p]] T) (hg : ∀ s : S, g s = s) (w : C ⊗[ℤ_[p]] T) (hw : w ∈ S.baseChange C) :
    g.baseChange C w = w := by
  obtain ⟨w, rfl⟩ := hw
  have h : g ∘ₗ S.subtype = S.subtype := LinearMap.ext hg
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h]

section Group

variable {G : PDivGroup p O} (e : G.Tate ≃ₗ[ℤ_[p]] P.T)

omit [IsAlgClosed C] [CharZero C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] in
theorem baseChange_symm_comp {N : Type} [AddCommGroup N] [Module ℤ_[p] N] (g : N →ₗ[ℤ_[p]] P.T)
    (x : O ⊗[ℤ_[p]] N) :
    e.toLinearMap.baseChange O ((e.symm.toLinearMap ∘ₗ g).baseChange O x) = g.baseChange O x := by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.comp_assoc,
    LinearEquiv.comp_symm, LinearMap.id_comp]

variable (SW : GlobalTheory.Published.ScholzeWeinsteinB) (K : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P)
  (hG : ∀ x, G.hodgeTateLinear x = 0 ↔ P.inclT (e.toLinearMap.baseChange O x) ∈ P.W)

include SW K hG

theorem exists_action_point : ∃ ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G,
    ∀ (a : Λ) t, e (ρ.onTate O (1 ⊗ₜ a) t) = P.actT a (e t) := by
  obtain ⟨ρ, hρ⟩ := exists_action SW P.integers G (e.symm.conjRingEquiv.toRingHom.comp P.actT)
    fun a x hx => (hG _).2 (by
      have h : (e.symm.conjRingEquiv.toRingHom.comp P.actT) a =
        e.symm.toLinearMap ∘ₗ (P.actT a ∘ₗ e.toLinearMap) := rfl
      rw [h, baseChange_symm_comp, LinearMap.baseChange_comp, LinearMap.comp_apply,
        inclT_baseChange]
      exact K.2.1 a _ ((hG x).1 hx))
  exact ⟨ρ, fun a t => by rw [hρ]; exact e.apply_symm_apply _⟩

variable [IsDomain O] {ε : PreTilt O p} {hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε}
  (H : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε) {ζ : (PDivGroup.mu p O).Tate}
  (hζ : Function.Bijective fun a : ℤ_[p] => a • ζ)

include H hζ

theorem exists_pol_point : ∃ pol : G ≅ G.dual, ∀ s t,
    pairing G O s (tateMap G G.dual O pol.hom t) = pairT P.A P.eps (e s) (e t) • ζ := by
  have hv := P.integers
  obtain ⟨B, hB, hB1, hB2⟩ := exists_form hv G ζ hζ
  have hk : KerIsLie G B := (GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G ζ B hv hζ hB).1
  have hβ : ∀ x z, LinearMap.BilinForm.baseChange O
      ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap) x z =
      LinearMap.BilinForm.baseChange O (pairT P.A P.eps) (e.toLinearMap.baseChange O x)
        (e.toLinearMap.baseChange O z) := fun x z => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
    | tmul c s =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul d t => simp
  have hb : Function.Bijective ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap).flip := by
    have h : ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap).flip =
      e.dualMap.toLinearMap ∘ₗ (pairT P.A P.eps).flip ∘ₗ e.toLinearMap := by
      ext s t; simp
    rw [h, LinearMap.coe_comp, LinearMap.coe_comp]
    exact e.dualMap.bijective.comp ((pairT_flip_bijective P).comp e.bijective)
  refine exists_pol SW hv H G ζ B hB hB1.2 hB2 hk
    ((pairT P.A P.eps).compl₁₂ e.toLinearMap e.toLinearMap) hb fun z => ?_
  rw [hG, inclT_mem_W_iff P K]
  refine ⟨fun h x hx => by rw [hβ, h _ ((hG x).1 hx)], fun h x hx => ?_⟩
  have h1 := baseChange_symm_comp P e LinearMap.id x
  rw [LinearMap.baseChange_id, LinearMap.id_apply] at h1
  rw [← h1, ← hβ]
  exact h _ ((hG _).2 (by rwa [h1]))

theorem exists_lie_point {G₁ : PDivGroup p O} (e₁ : G₁.Tate ≃ₗ[ℤ_[p]] P.tateGt)
    (l₁ : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G₁.Lie) (c : P.T →ₗ[ℤ_[p]] G₁.dual.Tate)
    (hc : ∀ s t, pairing G₁ O s (c t) = pairT P.A P.eps (e₁ s : P.T) t • ζ)
    (hl : ∀ x t, l₁ x (dlog G₁ (c t)) = (P.al₀ t).1 x) :
    ∃ i : G₁ ⟶ G, (∀ s, e (tateMap G₁ G O i s) = e₁ s) ∧ Function.Bijective (lieMap G₁ G i) := by
  have hv := P.integers
  obtain ⟨B, hB, hB1, -⟩ := exists_form hv G ζ hζ
  obtain ⟨B₁, hB₁, -, hB₁2⟩ := exists_form hv G₁ ζ hζ
  have hk : KerIsLie G B := (GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G ζ B hv hζ hB).1
  have hk₁ : KerIsLie G₁ B₁ := (GlobalTheory.T.hodge_tate_pairing_sandwich p C v O ε hε H G₁ ζ B₁ hv hζ hB₁).1
  obtain ⟨r, hr⟩ := exists_retraction_tateGt P
  obtain ⟨j, hj⟩ : ∃ j : G₁.Tate →ₗ[ℤ_[p]] P.T, ∀ s, j s = e₁ s :=
    ⟨P.tateGt.subtype ∘ₗ e₁.toLinearMap, fun _ => rfl⟩
  obtain ⟨r₁, hr'⟩ : ∃ r₁ : P.T →ₗ[ℤ_[p]] G₁.Tate, ∀ t, r₁ t = e₁.symm (r t) :=
    ⟨e₁.symm.toLinearMap ∘ₗ r, fun _ => rfl⟩
  have hr₁ : ∀ s, r₁ (j s) = s := fun s => by rw [hj, hr', hr, e₁.symm_apply_apply]
  have hc₁ : ∀ s t, B₁ s (c t) = pairT P.A P.eps (j s) t := fun s t => by
    rw [hj]
    exact hζ.1 ((hB₁ s _).symm.trans (hc s t))
  have hfix := baseChange_eq_self (C := C) P.tateGt (j ∘ₗ r₁) fun s => by
    rw [LinearMap.comp_apply, hj, hr', e₁.apply_symm_apply, hr]
  have he : Function.Injective (e.toLinearMap.baseChange O) := (e.baseChange ℤ_[p] O _ _).injective
  have h1 : ∀ s, (r₁ ∘ₗ e.toLinearMap) ((e.symm.toLinearMap ∘ₗ j) s) = s := fun s => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hr₁]
  have h2 : ∀ x, G₁.hodgeTateLinear x = 0 ↔
      G.hodgeTateLinear ((e.symm.toLinearMap ∘ₗ j).baseChange O x) = 0 := fun x => by
    rw [hG, baseChange_symm_comp]
    exact ker_iff_of_weil P K j r₁ hr₁ l₁ c B₁ hB₁2.1 hk₁ hc₁ hl x
  have h3 : ∀ x, G.hodgeTateLinear x = 0 → (e.symm.toLinearMap ∘ₗ j).baseChange O
      ((r₁ ∘ₗ e.toLinearMap).baseChange O x) = x := fun x hx => by
    refine he (inclT_injective P ?_)
    rw [baseChange_symm_comp, LinearMap.baseChange_comp, LinearMap.comp_apply,
      ← LinearMap.comp_apply (j.baseChange O), ← LinearMap.baseChange_comp, inclT_baseChange]
    exact hfix _ (K.2.2.2.1 ((hG x).1 hx))
  obtain ⟨i, hi, hi'⟩ := exists_lie_bijective SW hv H G G₁ ζ hζ.1 B hB hB1.2 hk _ _ h1 h2 h3
  exact ⟨i, fun s => by rw [hi, ← hj]; exact e.apply_symm_apply _, hi'⟩

end Group

theorem exists_selfDual_group : GlobalTheory.Published.ScholzeWeinsteinB → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P → ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.T) (ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G) (pol : G ≅ G.dual) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (tateMap G G.dual O pol.hom t) = pairT P.A P.eps (e s) (e t) • ζ) ∧ (∀ x t, l x (dlog (G := G) (tateMap G G.dual O pol.hom t)) = (P.al₀ (e t)).1 x) ∧ ∀ (a : Λ) t, e (ρ.onTate O (1 ⊗ₜ a) t) = P.actT a (e t) := by
  intro SW p _ C _ _ _ v O _ _ _ _ _ _ _ _ ε hε H Λ _ _ P K
  obtain ⟨G₁, e₁, l₁, c, ζ, hζ, hc, hl⟩ := GlobalTheory.T.exists_pdiv_group_for_point p C v O Λ P
  obtain ⟨G, e, hG⟩ := exists_group P SW
  obtain ⟨ρ, hρ⟩ := exists_action_point P e SW K hG
  obtain ⟨pol, hpol⟩ := exists_pol_point P e SW K hG H hζ
  obtain ⟨i, hi, hi'⟩ := exists_lie_point P e SW K hG H hζ e₁ l₁ c hc hl
  refine ⟨G, e, ρ, pol, l₁.trans (Equiv.ofBijective _ hi'), ζ, hζ, hpol, fun x t => ?_, hρ⟩
  have := isIntegrallyClosedIn_of_integers P.integers
  have h1 : tateMap _ _ O (dualHom G₁ G i) (tateMap G G.dual O pol.hom t) = c (e t) :=
    (G₁.pairing_flip_bijective C).1 (LinearMap.ext fun s => by
      rw [LinearMap.flip_apply, LinearMap.flip_apply, ← pairing_tateMap, hpol, hi, hc])
  rw [Equiv.trans_apply, Equiv.ofBijective_apply, lieMap_apply, ← dlog_tateMap, h1, hl]

end GlobalTheory.PointGroup
end

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_sandwich_lattice_rep : GlobalTheory.Published.ScholzeWeinsteinB → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P → ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.T) (ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G) (pol : G ≅ G.dual) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (tateMap G G.dual O pol.hom t) = pairT P.A P.eps (e s) (e t) • ζ) ∧ (∀ x t, l x (dlog (G := G) (tateMap G G.dual O pol.hom t)) = (P.al₀ (e t)).1 x) ∧ ∀ (a : Λ) t, e (ρ.onTate O (1 ⊗ₜ a) t) = P.actT a (e t) := by
  atlas_forward_decl GlobalTheory.PointGroup.exists_selfDual_group
end

section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_sandwich_star_rep : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.KernelShape P → (∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] P.T) (ρ : Action (ℤ_[p] ⊗[ℤ] Λ) G) (pol : G ≅ G.dual) (l : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt ≃ G.Lie) (ζ : (PDivGroup.mu p O).Tate), Function.Bijective (fun a : ℤ_[p] => a • ζ) ∧ (∀ s t, pairing G O s (tateMap G G.dual O pol.hom t) = pairT P.A P.eps (e s) (e t) • ζ) ∧ (∀ x t, l x (dlog (G := G) (tateMap G G.dual O pol.hom t)) = (P.al₀ (e t)).1 x) ∧ ∀ (a : Λ) t, e (ρ.onTate O (1 ⊗ₜ a) t) = P.actT a (e t)) → ∃ (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] Λ)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsTie P D (Algebra.TensorProduct.includeRight : Λ →ₐ[ℤ] ℤ_[p] ⊗[ℤ] Λ).toRingHom φ := by
  first | exact @GlobalTheory.DetInv.exists_isTie_of_selfDual | exact GlobalTheory.DetInv.exists_isTie_of_selfDual | (intros; apply GlobalTheory.DetInv.exists_isTie_of_selfDual <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory.PlaceShiftGlue

theorem bar_rt_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    IsCMField.complexConj E (H.rt : E) ≠ (H.rt : E) := by
  intro h
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h1 := IsCMField.complexEmbedding_complexConj E φ (H.rt : E)
  rw [h] at h1
  have h2 : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, RingOfIntegers.coe_eq_algebraMap, ← map_pow, H.rt_sq]; simp
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h1.symm
  rw [hr] at h2
  have h3 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h2
  have h4 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

open Classical in

theorem sum_two_weights {ι : Type} [Finite ι] (S : ι → Prop) (n : ι → ℕ) (κ : ι → ℝ) (κ₀ : ℝ) (a q : ℕ)
    (hn : ∀ i, n i = if S i then a else q) :
    ((a + q : ℕ) : ℝ) * κ₀ + ∑ᶠ i, (n i : ℝ) * κ i =
      a * (κ₀ + ∑ᶠ i, if S i then κ i else 0) + q * (κ₀ + ∑ᶠ i, if S i then 0 else κ i) := by
  haveI := Fintype.ofFinite ι
  simp only [finsum_eq_sum_of_fintype, mul_add, Finset.mul_sum]
  have : ∑ i, (n i : ℝ) * κ i =
      ∑ i, (a : ℝ) * (if S i then κ i else 0) + ∑ i, (q : ℝ) * (if S i then 0 else κ i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hn]
    split_ifs <;> simp
  rw [this]
  push_cast
  ring

theorem exists_height_eq {p : ℕ} [Fact p.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] {h : ℕ}
    (ρ : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]) : ∃ N, h = Module.finrank ℤ_[p] Λ * N := by
  haveI : Module.Free ℤ_[p] Λ := inferInstance
  obtain ⟨N, -, hN, -⟩ := GlobalTheory.DetInv.rep_free_charpoly p Λ h _ (Module.finBasis ℤ_[p] Λ) ρ
  exact ⟨N, hN.trans (mul_comm _ _)⟩

open Classical in

theorem shift_at_point (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
    (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (root ε).untilt p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E))
    (φ : P.V ≃ₗ[C] (Fin h → C))
    (hD : IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ)
    (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
    [FaithfulSMul ℤ_[p] Λ] (π : ℤ_[p] ⊗[ℤ] 𝓞 E →ₐ[ℤ_[p]] Λ) (e : ℤ_[p] ⊗[ℤ] 𝓞 E) (he : IsIdempotentElem e)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = Ideal.span {1 - e}) (t₀ : Λ →+* O) (γ : O ≃+* O)
    (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ)
    (hκ : ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), ∃ r : NNReal, r ≠ 0 ∧
      IsShift C v D ((γ : O →+* O).comp t₀) r ∧
      Real.log r = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ)
    (τ τ' : E →+* C) (hτ : ∀ a : 𝓞 E, γ (t₀ (π (1 ⊗ₜ a))) = embO P.integers τ a)
    (hτ' : (embO P.integers τ).comp (starRingEnd (𝓞 E)) = embO P.integers τ')
    (rt : 𝓞 E) (hrt : τ' (rt : E) ≠ τ (rt : E)) (a q : ℕ)
    (hrank : ∀ ψ : E →+* C, Module.finrank C (P.eigW (embO P.integers ψ)) =
      if ψ (rt : E) = τ (rt : E) then a else q)
    (x : Fin a → P.V) (y : Fin q → P.V) (g : Matrix (Fin a) (Fin a) C) (g' : Matrix (Fin q) (Fin q) C)
    (hx : Submodule.span O (Set.range x) = P.wRec (embO P.integers τ))
    (hy : Submodule.span O (Set.range y) = P.wRec ((embO P.integers τ).comp (starRingEnd (𝓞 E))))
    (hg : IsLatBasis C (P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) τ)
      (fun i => ∑ j, g i j • x j))
    (hg' : IsLatBasis C (P.latTSub ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • y j)) :
    Real.log (v g.det) - Real.log (v g'.det) =
      a * (κ₀ + ∑ᶠ σ : Λ →+* O, if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then κ σ else 0) +
      q * (κ₀ + ∑ᶠ σ : Λ →+* O, if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then 0 else κ σ) := by
  have hv := P.integers
  obtain ⟨hT, hH, hex, heig⟩ := GlobalTheory.T.datum_tie_number_field_point p C v O E P ε h D φ hε hD
  obtain ⟨h', D', iT, pT, iM, pM, hsp⟩ := GlobalTheory.T.idempotent_quotient_datum_compat p C v O hv ε hε _ Λ π e he hπ hk h D
  have hss := GlobalTheory.DetInv.part_rank_dim_shift p C v O hv ε hε _ Λ π e he hπ hk h h' D D' iT pT iM pM hsp hT hH
  obtain ⟨N, hN⟩ := exists_height_eq D'.ρT
  obtain ⟨r, hr0, hr, hlog⟩ := hκ N h' hN D'
  have hdim := (GlobalTheory.eig_decomp_T_H p C v O hv ε hε Λ N h' hN D').1.2.2 ((γ : O →+* O).comp t₀)
  obtain ⟨-, hd, hsh⟩ := hss ((γ : O →+* O).comp t₀)
  have ha : Module.finrank C (P.eigW (embO P.integers τ)) = a := by rw [hrank, if_pos rfl]
  have hq : Module.finrank C (P.eigW ((embO P.integers τ).comp (starRingEnd (𝓞 E)))) = q := by
    rw [hτ', hrank, if_neg hrt]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.datum_tie_hodge_tate_kernel p C v O E P ε h D φ hε hD _ τ r (RingHom.ext hτ) (hsh r hr) a q x y g g'
    ha hq hx hy hg hg'
  have hNa : N = a + q := by rw [← hdim, hd, h3]
  haveI := (GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ).1
  have hlie : ∀ σ : Λ →+* O, D'.lieRank ((γ : O →+* O).comp σ) =
      if σ (π (1 ⊗ₜ rt)) = t₀ (π (1 ⊗ₜ rt)) then a else q := fun σ => by
    obtain ⟨ψ, hψ⟩ := hex (((γ : O →+* O).comp σ).comp (π : ℤ_[p] ⊗[ℤ] 𝓞 E →+* Λ))
    rw [(hss _).1, (heig _ ψ hψ).2.2.2, hrank]
    have e1 : γ (σ (π (1 ⊗ₜ rt))) = embO P.integers ψ rt := RingHom.congr_fun hψ rt
    refine if_congr ?_ rfl rfl
    rw [← algebraMap_embO P.integers ψ, ← algebraMap_embO P.integers τ, ← e1, ← hτ,
      hv.hom_inj.eq_iff, γ.injective.eq_iff]
  have hg0 : ((v g'.det : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast (Valuation.ne_zero_iff v).2 h2
  have hr0' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  rw [h1, NNReal.coe_mul, Real.log_mul hr0' hg0, add_sub_cancel_right, hlog, hNa]
  exact sum_two_weights _ (fun σ => D'.lieRank ((γ : O →+* O).comp σ)) κ κ₀ a q hlie

theorem placeShift (hSW : GlobalTheory.Published.ScholzeWeinsteinB) (hPD : GlobalTheory.Published.PrismaticDieudonneHodge)
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint) : GlobalTheory.FlatCM.PlaceShiftSt := by
  classical
  intro E _ _ _ H _ ℓ _ w
  by_cases hw : ∃ τ₀ : E →+* ℂ_[ℓ], ∀ a : 𝓞 E, a ∈ w.asIdeal ↔ ‖τ₀ (a : E)‖ < 1
  swap
  · exact ⟨0, 0, fun τ hτ => (hw ⟨τ, hτ⟩).elim⟩
  obtain ⟨τ₀, hτ₀⟩ := hw
  obtain ⟨i1, i2, ε, hv, hε⟩ := PadicComplexHost.main ℓ
  obtain ⟨Λ, _, _, _, _, _, _, π, e, t₀, he, hπ, hk, ht₀, hall⟩ := GlobalTheory.PlaceRing.exists_placeRing E ℓ (embO hv τ₀)
  obtain ⟨κ₀, κ, hκ⟩ := GlobalTheory.T.dvr_embedding_determinant_value ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] hv ε hε Λ t₀
  refine ⟨κ₀ + ∑ᶠ σ : Λ →+* 𝓞_ℂ_[ℓ],
      @ite ℝ (σ (π (1 ⊗ₜ H.rt)) = t₀ (π (1 ⊗ₜ H.rt))) (Classical.propDecidable _) (κ σ) 0,
    κ₀ + ∑ᶠ σ : Λ →+* 𝓞_ℂ_[ℓ],
      @ite ℝ (σ (π (1 ⊗ₜ H.rt)) = t₀ (π (1 ⊗ₜ H.rt))) (Classical.propDecidable _) 0 (κ σ), fun τ hτ => ?_⟩
  letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ
  intro _ P a q hrank x x' g g' hx hx' hg hg'
  have hc : ∀ (ψ : E →+* ℂ_[ℓ]) (b : 𝓞 E), ((embO hv ψ b : 𝓞_ℂ_[ℓ]) : ℂ_[ℓ]) = ψ b := fun ψ b =>
    algebraMap_embO hv ψ b
  obtain ⟨t, ht⟩ := hall (embO hv τ) fun b => by rw [hc, hc, ← hτ, ← hτ₀]
  obtain ⟨γ, hγ, rfl⟩ := GlobalTheory.EmbConj.exists_isIsom_comp ℓ Λ t₀ t
  have hε' : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε := Dieudonne.isPrimitiveRoot_untilt_root hε
  have hS := GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne hPD ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] hv ε hε'
  have hP := (hK ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] (𝓞 E) P).2.2.2
  obtain ⟨h, D, φ, hD⟩ := GlobalTheory.T.hodge_tate_sandwich_star_rep ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] ε hε' hS (𝓞 E) P hP
    (GlobalTheory.T.hodge_tate_sandwich_lattice_rep hSW ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] ε hε' hS (𝓞 E) P hP)
  rw [← PadicComplexHost.valuation_coe_eq_norm, ← PadicComplexHost.valuation_coe_eq_norm]
  refine shift_at_point ℓ ℂ_[ℓ] Valued.v 𝓞_ℂ_[ℓ] E P ε hε h D φ hD Λ π e he hπ hk t₀ γ κ₀ κ (hκ γ hγ)
    τ (τ.comp (IsCMField.complexConj E).toAlgHom.toRingHom) ht ?_ H.rt ?_ a q hrank _ _ g g' hx hx' hg hg'
  · refine RingHom.ext fun b => hv.hom_inj ?_
    rw [RingHom.comp_apply, algebraMap_embO, algebraMap_embO]
    exact congrArg τ (H.bar_eq b)
  · exact fun h0 => bar_rt_ne H (τ.injective h0)

end GlobalTheory.PlaceShiftGlue

end
end

open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_shift_of_dieudonne : GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonneHodge → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → GlobalTheory.FlatCM.PlaceShiftSt := by
  atlas_forward_decl GlobalTheory.PlaceShiftGlue.placeShift
end

section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory

namespace GlobalTheory

theorem placeShiftSt_of_scholzeWeinstein (hP : GlobalTheory.CovTop.Hypotheses2) (hSW : GlobalTheory.Published.ScholzeWeinsteinB) :
    GlobalTheory.FlatCM.PlaceShiftSt :=
  GlobalTheory.T.place_shift_of_dieudonne hSW hP.q4 (GlobalTheory.T.hodge_tate_kernel_at_point hP)

end GlobalTheory
end
