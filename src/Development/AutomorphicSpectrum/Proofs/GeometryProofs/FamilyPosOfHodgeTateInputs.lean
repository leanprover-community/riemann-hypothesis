import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPreFamilyOfLatticeFamilyTwo
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBoundAllPlaces
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactStandardLattice
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionIntegrallyClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObjectStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.EqOfSpecializes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnramifiedPrimeIdempotent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HTChartExistsHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFreeIntegralModels
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsIntegrallyClosedOfDenom
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModelBaseChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualBaseChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FullTorsionPacking
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeDegree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeCount
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeTotal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestOrderSections
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelHodgeRelay
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestCharacterExists
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TeichmullerTestFunction
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestLeafLattice
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestLiftExists
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestGroupPointExists
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBaseChangeLargerRingHolds
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemFirstLatticeIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ValMulLeOfCyclicKer
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeKernelImageLattice
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianFactorTightFieldAction
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientZarhinHodgeTateSubquotient

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.Orbit

section Ring

variable {Ω : Type} [Field Ω] {A : Type} [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
  {m : Ideal A} [m.IsPrime] {O : Type} [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
  [IsScalarTower A O Ω]

include m in

theorem algebraMap_injective : Function.Injective (algebraMap O Ω) := by
  have hA : Function.Injective (algebraMap A Ω) := IsIntegralClosure.algebraMap_injective A ℤ Ω
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq m.primeCompl x
  have h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap A Ω (s : A) = algebraMap A Ω a := by
    rw [IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω a, ← map_mul,
      IsLocalization.mk'_spec]
  rw [hx, zero_mul] at h1
  have h2 : a = 0 := hA (by rw [← h1, map_zero])
  rw [h2, IsLocalization.mk'_zero]

include m in

theorem exists_of_integral (x : Ω) (hx : IsIntegral ℤ x) : ∃ o : O, algebraMap O Ω o = x :=
  ⟨algebraMap A O (IsIntegralClosure.mk' A x hx), by
    rw [← IsScalarTower.algebraMap_apply, IsIntegralClosure.algebraMap_mk']⟩

include m in

theorem exists_hom {R : Type} [CommRing R] (f : R →+* Ω) (hf : ∀ a, IsIntegral ℤ (f a)) :
    ∃ g : R →+* O, ∀ a, algebraMap O Ω (g a) = f a := by
  have hi := algebraMap_injective (Ω := Ω) (A := A) (m := m) (O := O)
  choose g hg using fun a => exists_of_integral (Ω := Ω) (A := A) (m := m) (O := O) (f a) (hf a)
  exact ⟨{ toFun := g
           map_one' := hi (by rw [hg, map_one, map_one])
           map_mul' := fun a b => hi (by rw [hg, map_mul, map_mul, hg, hg])
           map_zero' := hi (by rw [hg, map_zero, map_zero])
           map_add' := fun a b => hi (by rw [hg, map_add, map_add, hg, hg]) }, hg⟩

end Ring

theorem sub_one_pow_eq {O : Type} [CommRing O] [IsDomain O] {p : ℕ} (hp : p.Prime) {ζ : O}
    (h : IsPrimitiveRoot ζ p) : ∃ u : O, IsUnit u ∧ (ζ - 1) ^ (p - 1) = u * (p : O) := by
  have h1 : IsPrimitiveRoot ζ ((p - 1) + 1) := by rwa [Nat.sub_add_cancel hp.one_le]
  have h2 := h1.prod_one_sub_pow_eq_order
  have h3 : Associated (∏ _k ∈ Finset.range (p - 1), (ζ - 1))
      (∏ k ∈ Finset.range (p - 1), (1 - ζ ^ (k + 1))) := by
    refine Associated.prod _ _ _ fun k hk => ?_
    have hk' : k + 1 < p := by have := Finset.mem_range.1 hk; have := hp.one_le; omega
    have hc : (k + 1).Coprime p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_of_pos_of_lt (by omega) hk'))
    have := h.associated_sub_one_pow_sub_one_of_coprime hc
    have e : (1 - ζ ^ (k + 1)) = - (ζ ^ (k + 1) - 1) := by ring
    rw [e]
    exact this.trans (Associated.refl _).neg_right
  rw [h2, Finset.prod_const, Finset.card_range] at h3
  obtain ⟨u, hu⟩ := h3
  refine ⟨((u⁻¹ : Oˣ) : O), Units.isUnit _, ?_⟩
  have e1 : (((p - 1 : ℕ) : O) + 1) = (p : O) := by
    rw [← Nat.cast_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp.one_le]
  have hu' : (ζ - 1) ^ (p - 1) * (u : O) = (p : O) := by
    rw [hu]; first | exact e1 | (push_cast; exact e1)
  rw [← hu', mul_comm]
  exact (Units.mul_inv_cancel_right _ _).symm

section Abstract

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField in

theorem orbit_abstract {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ NumberField.discr E) {T : Type} [Finite T] (t₀ : T)
    (φ : Equiv.Perm T) {k : Type} [Field k] (r : T → 𝓞 E →+* k) (hpk : (p : k) = 0)
    (hF : ∀ s a, r (φ s) a = (r s a) ^ p) :
    ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → T) (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F)
      (_ : CharP F p) (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}))
      (σ : Sg → F →+* k), t₀ ∈ Set.range e ∧ Function.Injective e ∧ (∀ τ, e (φ' τ) = φ (e τ)) ∧
        Function.Surjective pq ∧ (∀ τ a, r (e τ) a = σ τ (pq (Ideal.Quotient.mk _ a))) ∧
        (∀ t, (∀ a, r t a = 0 ↔ pq (Ideal.Quotient.mk _ a) = 0) → t ∈ Set.range e) ∧ IsSec pq sc := by
  classical
  set w₀ : Ideal (𝓞 E) := RingHom.ker (r t₀) with hw₀
  haveI hprime : w₀.IsPrime := RingHom.ker_isPrime _
  have hpw : (p : 𝓞 E) ∈ w₀ := by
    rw [hw₀, RingHom.mem_ker, map_natCast, hpk]
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hne : w₀ ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hpw)
  haveI hmax : w₀.IsMaximal := Ideal.IsPrime.isMaximal hprime hne
  letI fld : Field (𝓞 E ⧸ w₀) := Ideal.Quotient.field w₀
  haveI hfinq : Finite (𝓞 E ⧸ w₀) := Ideal.finiteQuotientOfFreeOfNeBot w₀ hne
  letI fin : Fintype (𝓞 E ⧸ w₀) := Fintype.ofFinite _
  have hle : Ideal.span {(p : 𝓞 E)} ≤ w₀ := (Ideal.span_singleton_le_iff_mem _).2 hpw
  have hchar : CharP (𝓞 E ⧸ w₀) p := by
    haveI : Fact p.Prime := ⟨hp⟩
    refine (CharP.charP_iff_prime_eq_zero hp).2 ?_
    have : ((p : 𝓞 E) : 𝓞 E ⧸ w₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hpw
    simpa using this
  have hker : ∀ s, RingHom.ker (r (φ s)) = RingHom.ker (r s) := fun s => by
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker, hF, pow_eq_zero_iff hp.ne_zero]
  obtain ⟨ε, h1, -, h3, -, -⟩ := unramified_prime_idempotent E p hp hd w₀ hpw
  have hsurj : Function.Surjective (Ideal.Quotient.mk w₀) := Ideal.Quotient.mk_surjective
  let lf : (𝓞 E ⧸ w₀) → 𝓞 E := Function.surjInv hsurj
  have hlf : ∀ a, Ideal.Quotient.mk w₀ (lf a) = a := Function.surjInv_eq hsurj
  let pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* (𝓞 E ⧸ w₀) := Ideal.Quotient.factor hle
  have hpq : ∀ a, pq (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk w₀ a := fun a => rfl
  have hz : ∀ a ∈ w₀, Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) (ε * a) = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ((h3 a).2 ha))
  let sc : (𝓞 E ⧸ w₀) →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) :=
    AddMonoidHom.mk' (fun a => Ideal.Quotient.mk _ (ε * lf a)) fun a b => by
      have hm : lf (a + b) - (lf a + lf b) ∈ w₀ := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add, hlf, hlf, hlf, sub_self]
      have := hz _ hm
      rw [mul_sub, map_sub, sub_eq_zero, mul_add, map_add] at this
      exact this
  have hsc : ∀ a, sc a = Ideal.Quotient.mk _ (ε * lf a) := fun a => rfl
  let Sg : Type := {t : T // RingHom.ker (r t) = w₀}
  let f : Sg → Sg := fun τ => ⟨φ τ.1, (hker τ.1).trans τ.2⟩
  have hfi : Function.Injective f := fun a b h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h))
  haveI : Finite Sg := inferInstance
  let φ' : Equiv.Perm Sg := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
  let σ : Sg → (𝓞 E ⧸ w₀) →+* k := fun τ => Ideal.Quotient.lift w₀ (r τ.1) fun a ha => by
    have : a ∈ RingHom.ker (r τ.1) := by rw [τ.2]; exact ha
    exact this
  refine ⟨Sg, Fintype.ofFinite Sg, Subtype.val, φ', 𝓞 E ⧸ w₀, fld, fin, hchar, pq, sc, σ, ⟨⟨t₀, rfl⟩, rfl⟩,
    Subtype.val_injective, fun τ => rfl, Ideal.Quotient.factor_surjective hle, fun τ a => rfl, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨⟨t, ?_⟩, rfl⟩
    ext a
    rw [RingHom.mem_ker, ht a, hpq, Ideal.Quotient.eq_zero_iff_mem]
  · intro a
    rw [hsc, hpq, map_mul, hlf]
    have : Ideal.Quotient.mk w₀ ε = 1 := by
      rw [← map_one (Ideal.Quotient.mk w₀)]
      exact Ideal.Quotient.eq.2 h1
    rw [this, _root_.one_mul]
  · intro u a hu
    obtain ⟨u', rfl⟩ := Ideal.Quotient.mk_surjective u
    have hu' : u' ∈ w₀ := Ideal.Quotient.eq_zero_iff_mem.1 hu
    rw [hsc, ← map_mul]
    have := hz _ (w₀.mul_mem_right (lf a) hu')
    rw [show u' * (ε * lf a) = ε * (u' * lf a) by ring]
    exact this

end Abstract

section Root

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem exists_point (A : HodgeCpt Y S y) : ∃ x : Sp Ω ⟶ Xo.XF c, A.ξ ≫ A.f = x ≫ Y.j := by
  have : IsProper Y.s := projProper O₀ Y.X Y.s Y.proj
  have : IsLocallyNoetherian (pullback Y.s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap β))
  have : CompactSpace ↥(pullback Y.s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap β))
  have : IsNoetherian (pullback Y.s (spMap β)) := {}
  have := Y.jQ_open
  let pt₀ : Sp Ω ⟶ pullback Y.s (spMap β) := pullback.lift (A.ξ ≫ A.f) (spMap A.cst) (by
    rw [Category.assoc, A.cst_over]; exact Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom A.cst))
  have hpt₀ : pt₀ ≫ pullback.fst _ _ = A.ξ ≫ A.f := pullback.lift_fst _ _ _
  have hpt : pullback.fst Y.s (spMap β) (pt₀ (IsLocalRing.closedPoint Ω)) = genPt A.ξ₀ := by
    have : Subsingleton (Spec (CommRingCat.of A.Ω₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum A.Ω₀))
    have h0 : pt₀ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom A.fn) ≫ A.ξ₀ := hpt₀.trans A.fn_over
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    rw [h0]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg A.ξ₀ (Subsingleton.elim _ _))
  obtain ⟨q, hqU, hq⟩ := GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag.exists_gen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense
    (pt₀ (IsLocalRing.closedPoint Ω))
  have h1 := hq.map (pullback.fst Y.s (spMap β)).continuous
  rw [hpt] at h1
  have h2 := GlobalTheory.CompanionTheory.Ar.CmpHodgeDiag.eq_of_specializes A.gen₀ h1
  have hr : Set.range pt₀ ⊆ Set.range Y.jQ := by
    rintro _ ⟨a, rfl⟩
    have : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    rw [Subsingleton.elim a (IsLocalRing.closedPoint Ω), ← Y.ab_gen, Set.mem_preimage, hpt, ← h2]
    have h3 : q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact hqU
    exact h3
  refine ⟨IsOpenImmersion.lift Y.jQ pt₀ hr, ?_⟩
  rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hpt₀]

theorem exists_root (A : HodgeCpt Y S y) (hpq : 0 < D.p + D.q) {p : ℕ} (hp : p.Prime) (hpS : p ∈ S) :
    ∃ ζ : Ω, IsPrimitiveRoot ζ p := by
  haveI : CharZero Ω := charZero_of_injective_ringHom A.cst.injective
  obtain ⟨x, hx⟩ := exists_point A
  obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c O₀ β Y A.X A.f A.t A.m Ω A.ξ x hx
  have hN : 0 < p ^ A.R p := pow_pos hp.pos _
  obtain ⟨ζ, hζ⟩ := GlobalTheory.CompanionTheory.Ar.OmLink.root o A.t m0 (A.tors p hpS) hN hpq
  have hR : 1 ≤ A.R p := by have := A.R_ge p hpS; omega
  refine ⟨ζ ^ (p ^ (A.R p - 1)), hζ.pow hN ?_⟩
  rw [← pow_succ, Nat.sub_add_cancel hR]

end Root

theorem orbit_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ t₀ : CMType H ⊕ CMType H, ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F p) (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ ∧ IsSec pq sc := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ hpq p hfact hpS _ hp2 hdisc φ hφ A _ _ _ m _ hpm O _ _ _ _ _ _ _ t₀
  have hp : p.Prime := hfact.out
  have hinj := algebraMap_injective (Ω := Ω) (A := A) (m := m) (O := O)
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨ζ, hζ⟩ := exists_root 𝔐 hpq hp hpS
  have hζi : IsIntegral ℤ ζ := IsIntegral.of_pow hp.pos (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  obtain ⟨z, hz⟩ := exists_of_integral (A := A) (m := m) (O := O) ζ hζi
  have hzp : IsPrimitiveRoot z p :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap O Ω) (by rwa [hz]) hinj
  obtain ⟨u, hu, huw⟩ := sub_one_pow_eq hp hzp
  choose g hg using fun t => exists_hom (A := A) (m := m) (O := O) (𝔐.emb t)
    (fun a => (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.emb t).toIntAlgHom)
  have hpm' : (p : O) ∈ IsLocalRing.maximalIdeal O := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hpm
    simpa using this
  have hnu : ¬ IsUnit (p : O) := hpm'
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h1 : algebraMap O Ω (p : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h1
    exact hp.ne_zero (Nat.cast_eq_zero.1 h1)
  have hpk : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (p : O)).2 hpm'
    simpa using this
  obtain ⟨inc, hinc⟩ := exists_hom (A := A) (m := m) (O := O) (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))
    (fun a => (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toIntAlgHom)
  have hel : ∀ s (a : 𝓞 E), ∃ v : 𝓞 c.F, (v : c.F) = labelEmb c s a ∧ inc v = g s a := by
    intro s a
    have hi : IsIntegral ℤ (labelEmb c s a) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map (labelEmb c s).toIntAlgHom
    refine ⟨IsIntegralClosure.mk' _ _ hi, IsIntegralClosure.algebraMap_mk' _ _ _, hinj ?_⟩
    rw [hinc, hg, RingHom.comp_apply, IsIntegralClosure.algebraMap_mk']
    rfl
  have hF : ∀ s (a : 𝓞 E), IsLocalRing.residue O (g (φ s) a) = (IsLocalRing.residue O (g s a)) ^ p := by
    intro s a
    obtain ⟨u', hu1, hu2⟩ := hel (φ s) a
    obtain ⟨v', hv1, hv2⟩ := hel s a
    have hn := hφ (Ideal.comap inc (IsLocalRing.maximalIdeal O)) inferInstance
      (by rw [Ideal.mem_comap, map_natCast]; exact hpm') s a u' v' hu1 hv1
    rw [Ideal.mem_comap, map_sub, map_pow, hu2, hv2] at hn
    have h2 := (IsLocalRing.residue_eq_zero_iff _).2 hn
    rw [map_sub, map_pow, sub_eq_zero] at h2
    exact h2
  obtain ⟨Sg, i1, e, φ', F, i2, i3, i4, pq, sc, σ, a1, a2, a3, a4, a5, a6, a7⟩ :=
    orbit_abstract hp hdisc t₀ φ (fun t => (IsLocalRing.residue O).comp (g t)) hpk hF
  refine ⟨Sg, i1, e, φ', F, i2, i3, i4, pq, sc, z - 1, σ, ⟨a1, a2, a3, a4, ?_, ?_, ⟨hp0, ⟨u, hu, huw⟩, hnu⟩, ?_⟩, a7⟩
  · intro τ a
    exact ⟨g (e τ) a, hg _ _, a5 τ a⟩
  · intro t ht
    exact a6 t fun a => ht a (g t a) (hg t a)
  · unfold HT.IsCp
    rw [if_neg hp2]
    exact ⟨ζ, hζ, by rw [map_sub, map_one, hz]⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.Orbit
end
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_hodge_prime_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ t₀ : CMType H ⊕ CMType H, ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F p) (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ ∧ IsSec pq sc := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.Orbit.orbit_exists
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts

theorem chartRing_over_place_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ ∃ x : Spec (CommRingCat.of (CR O y c')) ⟶ 𝔐.X, spMap (algebraMap (CR O y c') Ω) ≫ x = 𝔐.ξ :=
  @PositivityTheory.Xgn.torsion_packing_facts

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_torsion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ ∃ x : Spec (CommRingCat.of (CR O y c')) ⟶ 𝔐.X, spMap (algebraMap (CR O y c') Ω) ≫ x = 𝔐.ξ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.ChartFacts.chartRing_over_place_facts
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie

theorem lieModel_along_generic : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li) (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li), M₀.IsActOf act.act ρ₀ → ∀ (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L) (toLi : L →ₗ[R] Li), Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧ (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧ ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  intro X G _ _ _ Ω _ ξ Li _ _ M₀ B _ act ρ₀ h₀ O _ _ R x hx
  subst hx
  obtain ⟨L, iL, mL, ⟨M⟩⟩ := lieModel_exists X G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act X G R x L M B act.act act.hom act.one act.mul act.add
  have hsm : ∀ (a : R) (t : Li), a • t = algebraMap R Ω a • t := fun _ _ => rfl
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ x = spMap (algebraMap R Ω) ≫ x := rfl
  have ex : ∀ e, ∃ t, M₀.pt t = LieTangent.epsBase (algebraMap R Ω) hφ ≫ M.pt e :=
    fun e => M₀.onto _ (LieTangent.isTanAt_base _ hφ (M.tan e))
  choose f hf using ex
  let j : L →ₗ[R] Li :=
    { toFun := f
      map_add' := fun a b => M₀.inj (by rw [M₀.add, hf, hf, hf, M.add, comp_mul])
      map_smul' := fun c e => M₀.inj (by
        rw [RingHom.id_apply, hsm, LieModel.pt_smul, hf, hf, LieModel.pt_smul, ← Category.assoc,
          LieTangent.base_scale, Category.assoc]) }
  have hl : ∀ v, (M₀.pt (j v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left := fun v => by
    change (M₀.pt (f v)).left = _
    rw [hf]
    rfl
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.lie_model_finite_base_change X G R x L M
  refine ⟨L, iL, mL, M, ρ, j, h1, h2, hρ, h3 Ω Li M₀ j hl, hl, fun a v => M₀.inj ?_⟩
  change M₀.pt (f (ρ a v)) = M₀.pt (ρ₀ a (f v))
  rw [h₀ a, hf, hf, hρ a, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_action_subalgebra : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li) (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li), M₀.IsActOf act.act ρ₀ → ∀ (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L) (toLi : L →ₗ[R] Li), Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧ (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧ ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie.lieModel_along_generic
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dual_baseChange_fractionField : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) :=
  @PositivityTheory.Xgn.exists_dual_base_change

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_base_change : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.dual_baseChange_fractionField
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem torsionAlong_of_fullTorsion : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsNoetherianRing R] [CharZero R] [IsFractionRing R Ω] (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∀ (T : Type) [CommGroup T] (pt : T →* (Over.mk ξ ⟶ G)) (N n : ℕ), 1 ≤ N → N ∣ n → FullTorsion G ξ n → Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (pt t).left = spMap (fracToField R) ≫ (Γ.pt t).left ≫ i :=
  @PositivityTheory.Xgn.full_torsion_packing

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_torsion_injective_subalgebra : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsNoetherianRing R] [CharZero R] [IsFractionRing R Ω] (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∀ (T : Type) [CommGroup T] (pt : T →* (Over.mk ξ ⟶ G)) (N n : ℕ), 1 ≤ N → N ∣ n → FullTorsion G ξ n → Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (pt t).left = spMap (fracToField R) ≫ (Γ.pt t).left ≫ i := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.torsionAlong_of_fullTorsion
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx

theorem lie_pack (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li)
    (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li) (h₀ : M₀.IsActOf act.act ρ₀)
    (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω]
    (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap (algebraMap R Ω) ≫ x = ξ) :
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L)
      (toLi : L →ₗ[R] Li) (j : Module.Dual R L →ₗ[R] Module.Dual Ω Li),
      Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧
      (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧
      IsBaseChange Ω j ∧ (∀ u v, j u (toLi v) = algebraMap R Ω (u v)) ∧
      ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  obtain ⟨L, i1, i2, M, ρ, toLi, hf, hp, ha, hb, hpt, hρ⟩ := GlobalTheory.T.lie_model_action_subalgebra X G Ω ξ Li M₀ B act ρ₀ h₀ O R x hx
  obtain ⟨j, hj, hj'⟩ := GlobalTheory.T.dual_lattice_base_change Ω O R L Li toLi hb
  exact ⟨L, i1, i2, M, ρ, toLi, j, hf, hp, ha, hb, hpt, hj, hj', hρ⟩

theorem isIso_spMap_fracToField {Ω : Type} [Field Ω] {O : Type} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω)
    [IsFractionRing R Ω] : IsIso (spMap (fracToField R)) := by
  have hs : Function.Surjective (fracToField R) := fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    refine ⟨algebraMap R (FractionRing R) a / algebraMap R (FractionRing R) b, ?_⟩
    have h : ∀ r : R, fracToField R (algebraMap R (FractionRing R) r) = algebraMap R Ω r := fun r =>
      IsFractionRing.lift_algebraMap _ r
    rw [map_div₀, h, h]
  have : IsIso (CommRingCat.ofHom (fracToField R)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(fracToField R).injective, hs⟩
  infer_instance

theorem finite_torsT (E : Type) [Field E] [NumberField E] (N n : ℕ) (hn : n ≠ 0) : Finite (TorsT E N n) := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  exact inferInstanceAs (Finite (Fin N → (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)})))

theorem qhom_surjective (E : Type) [Field E] [NumberField E] (N n : ℕ) : Function.Surjective (qhom (E := E) N n) := fun t => by
  choose f hf using fun i => Ideal.Quotient.mk_surjective (Multiplicative.toAdd t i)
  refine ⟨Multiplicative.ofAdd f, ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  exact hf i

theorem qhom_eq_one_iff (E : Type) [Field E] [NumberField E] (N n : ℕ) (y : Fin N → 𝓞 E) :
    qhom (E := E) N n (Multiplicative.ofAdd y) = 1 ↔ ∃ y', y = n • y' := by
  have h1 : qhom (E := E) N n (Multiplicative.ofAdd y) = 1 ↔ ∀ i, (n : 𝓞 E) ∣ y i := by
    constructor
    · intro h i
      have h2 := congrFun (congrArg Multiplicative.toAdd h) i
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
    · intro h
      apply Multiplicative.toAdd.injective
      funext i
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h i))
  rw [h1]
  constructor
  · intro h
    choose f hf using h
    exact ⟨f, by funext i; simp [hf i, nsmul_eq_mul]⟩
  · rintro ⟨y', rfl⟩ i
    exact ⟨y' i, by simp [nsmul_eq_mul]⟩

theorem chartPack_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → Nonempty (ChartPack G O c') := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hv hpq p _ hpS hHT hp2 hdisc A _ _ _ m _ hm O _ _ _ _ _ _ _ G c' hc
  obtain ⟨hΩ, hno, hic, hfr, x, hx⟩ := GlobalTheory.T.arith_variety_prime_torsion E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hv p hpS A m hm O c' hc
  haveI := hno; haveI := hic; haveI := hfr; haveI := hΩ
  haveI : CharZero (CR O y c') := ⟨fun a b h => by
    have h2 := congrArg (algebraMap (CR O y c') Ω) h
    simpa using h2⟩
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨L, i1, i2, M, ρ, toLi, j, hfin, hproj, hact, hbc, hpt, hjbc, hj, hρ⟩ :=
    lie_pack 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M (𝓞 E) 𝔐.t.act 𝔐.ρ 𝔐.act O (CR O y c') x hx
  have hR : 0 < 𝔐.R p := by have := 𝔐.R_ge p hpS; omega
  obtain ⟨Γ₁, i₁, ht₁, hp₁⟩ := GlobalTheory.T.full_torsion_injective_subalgebra 𝔐.X 𝔐.t.G 𝔐.t.semi Ω 𝔐.ξ O (CR O y c') x hx _ G.t₁.pt p (p ^ 𝔐.R p)
    (Fact.out : p.Prime).one_lt.le (dvd_pow_self p hR.ne') (𝔐.tors p hpS) G.t₁.inj G.t₁.onto
  obtain ⟨Γ₂, i₂', ht₂, hp₂⟩ := GlobalTheory.T.full_torsion_injective_subalgebra 𝔐.X 𝔐.t.G 𝔐.t.semi Ω 𝔐.ξ O (CR O y c') x hx _ G.t₂.pt (p ^ 𝔐.R p) (p ^ 𝔐.R p)
    (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos) dvd_rfl (𝔐.tors p hpS) G.t₂.inj G.t₂.onto
  have hn0 : p ^ 𝔐.R p ≠ 0 := (pow_pos (Fact.out : p.Prime).pos _).ne'
  have hmem : ∀ z : Ω, z ^ (p ^ 𝔐.R p) = 1 → z ∈ CR O y c' := fun z hz => by
    have hi : IsIntegral ℤ z := IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) (hz ▸ isIntegral_one)
    have h := IsIntegralClosure.algebraMap_mk' A z hi
    rw [← h, IsScalarTower.algebraMap_apply A O Ω]
    exact (CR O y c').algebraMap_mem _
  have hz1 : G.ζ ^ (p ^ 𝔐.R p) = 1 := G.ζ_prim.pow_eq_one
  have hz2 : (G.ζ⁻¹) ^ (p ^ 𝔐.R p) = 1 := by rw [inv_pow, hz1, inv_one]
  have hne : G.ζ ≠ 0 := G.ζ_prim.ne_zero hn0
  obtain ⟨ζ, hζ⟩ : ∃ u : (CR O y c')ˣ, ((u : CR O y c') : Ω) = G.ζ :=
    ⟨⟨⟨G.ζ, hmem _ hz1⟩, ⟨G.ζ⁻¹, hmem _ hz2⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩
  haveI hfinT : Finite (TorsT E (D.p + D.q) (p ^ 𝔐.R p)) := finite_torsT E _ _ hn0
  have hsurj : Function.Surjective (qhom (E := E) (D.p + D.q) (p ^ 𝔐.R p)) := qhom_surjective E _ _
  have hker : ∀ y₁, qhom (E := E) (D.p + D.q) (p ^ 𝔐.R p) (Multiplicative.ofAdd y₁) = 1 ↔ ∃ y', y₁ = (p ^ 𝔐.R p) • y' :=
    qhom_eq_one_iff E _ _
  haveI hiso := isIso_spMap_fracToField (CR O y c')
  have hlin : ∀ (a : 𝓞 E) y₁, (Γ₂.pt (qhom _ _ (Multiplicative.ofAdd (a • y₁)))).left ≫ i₂' =
        (Γ₂.pt (qhom _ _ (Multiplicative.ofAdd y₁))).left ≫ i₂' ≫ (𝔐.t.act.act a).left := by
    intro a y₁
    rw [← cancel_epi (spMap (fracToField (CR O y c')))]
    have h1 := hp₂ (qhom _ _ (Multiplicative.ofAdd (a • y₁)))
    have h2 := hp₂ (qhom _ _ (Multiplicative.ofAdd y₁))
    have h3 : (G.t₂.pt (qhom _ _ (Multiplicative.ofAdd (a • y₁)))).left =
        (G.t₂.pt (qhom _ _ (Multiplicative.ofAdd y₁))).left ≫ (𝔐.t.act.act a).left :=
      congrArg (fun f => f.left) (G.t₂.lin a y₁)
    rw [← h1, h3, h2]
    simp only [Category.assoc]
  have hzpow : ζ ^ (p ^ 𝔐.R p) = 1 := by
    apply Units.ext
    apply Subtype.ext
    show (((ζ : CR O y c') ^ (p ^ 𝔐.R p) : CR O y c') : Ω) = 1
    rw [SubmonoidClass.coe_pow, hζ, hz1]
  have hbar : ∀ a : 𝓞 E, RingOfIntegers.mapRingEquiv (HT.cmConj E) a = H.bar a := fun a => by
    ext
    rw [H.bar_eq]
    rfl
  obtain ⟨Dh, hDe, hHT⟩ := GlobalTheory.T.HTChartExists_holds (CR O y c') Ω E (HT.cmConj E) p (𝔐.R p) (D.p + D.q) _ Γ₂ 𝔐.X 𝔐.t.G x i₂' ht₂ hsm
    𝔐.t.act.act 𝔐.t.act.hom L M ρ hact (Module.Dual Ω 𝔐.Li) j hjbc (qhom _ _) hsurj hker hlin ζ hzpow G.e G.alt
    (fun a y₁ z => by rw [hbar]; exact G.adj a y₁ z) G.e_surj G.e_inj
  have hform : ∀ (b : 𝓞 E) (w : Module.Dual (CR O y c') L), j (w ∘ₗ ρ b) = j w ∘ₗ 𝔐.ρ b := by
    intro b w
    ext e
    refine hbc.inductionOn e (fun e => j (w ∘ₗ ρ b) e = (j w ∘ₗ 𝔐.ρ b) e) (by simp) ?_ ?_ ?_
    · intro v
      simp only [LinearMap.comp_apply]
      rw [hj, ← hρ, hj]
      rfl
    · intro s n hn
      simp only [map_smul, hn]
    · intro n₁ n₂ h₁ h₂
      simp only [map_add, h₁, h₂]
  have hact' : ∀ (a : 𝓞 E) (u : Module.Dual Ω 𝔐.Li), Dh.ρΩ a u = u ∘ₗ 𝔐.ρ (H.bar a) := by
    intro a u
    refine hjbc.inductionOn u (fun u => Dh.ρΩ a u = u ∘ₗ 𝔐.ρ (H.bar a)) (by simp) ?_ ?_ ?_
    · intro w
      rw [hHT.2.1, hbar, hform]
    · intro s n hn
      rw [map_smul, hn]
      rfl
    · intro n₁ n₂ h₁ h₂
      rw [map_add, h₁, h₂]
      rfl
  exact ⟨{ x := x, x_gen := hx, L := L, fin := hfin, proj := hproj, M := M, ρ := ρ, act := hact, toLi := toLi, toLi_bc := hbc,
           toLi_pt := hpt, j := j, j_bc := hjbc, j_apply := hj, Γ₁ := Γ₁, i₁ := i₁, tors₁ := ht₁, pts₁ := hp₁,
           Γ₂ := Γ₂, i₂ := i₂', tors₂ := ht₂, pts₂ := hp₂, ζ := ζ, ζ_eq := hζ, Dh := Dh, Dh_e := hDe, Dh_act := hact', isHT := hHT }⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx
end
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_hodge_prime_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → Nonempty (ChartPack G O c') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackEx.chartPack_exists
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  first | exact @PositivityTheory.Xgn.test_order_sections | exact PositivityTheory.Xgn.test_order_sections
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_global_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∃ (AA : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)) (AW : ReciprocityTheory.PGsh.L2.HopfOrder (C := C) RC (Fin (D.p + D.q) → F)), AA.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) ∧ AW.carrier = (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) ∧ AW.carrier.toAddSubgroup = ((chartD e b pq sc w P i).bc RC).M ∧ (∀ h ∈ AA.carrier, (fun x => h ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.toNAdd sc) ((GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.fromNAdd pq) x))) ∈ AA.carrier) ∧ GlobalTheory.CompanionTheory.Ar.GR.FStable F AW.carrier := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.arith_variety_prime_global_relay
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem lifts_eq_frobenius_powers : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) :=
  @PositivityTheory.Xgn.test_character_exists

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_total : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∃ (σ' : MulChar F RC) (ee : Sg → ℕ), GlobalTheory.CompanionTheory.Ar.GR.IsFund p σ' ∧ (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) ∧ ∀ τ, σ' ^ p ^ ee (φ' τ) = σ' ^ p ^ (ee τ + 1) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.lifts_eq_frobenius_powers
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] (σ' : MulChar F RC) (ee : Sg → ℕ), (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) → ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)) := by
  first | exact @PositivityTheory.Xgn.teichmuller_test_function | exact PositivityTheory.Xgn.teichmuller_test_function
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] (σ' : MulChar F RC) (ee : Sg → ℕ), (∀ τ a, χ τ a = ((σ' ^ p ^ ee τ) a : RC)) → ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), χ τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC) (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrdW P sc RC)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem w_mul_forms_le_af : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) → ∀ τ, mulLat (algebraMap O C w) (stdLat RC _) ≤ ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) := by
  exact @PositivityTheory.Xgn.test_leaf_lattice

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_model_prime_total : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → GlobalTheory.CompanionTheory.Ar.GR.IsAbFactor p (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testOrd P RC) → ∀ τ, mulLat (algebraMap O C w) (stdLat RC _) ≤ ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.w_mul_forms_le_af
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

theorem GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ τ, ∃ hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C)), Function.Injective hb ∧ LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) ∧ (stdLat RC _).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).omHT τ ∧ (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ ∧ (∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔ (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈ ((chartD e b pq sc w P i).bc RC).omHT τ) ∧ (∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔ (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧ b' - hb a ∈ stdLat RC _) ∧ ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _) :=
  @PositivityTheory.Xgn.test_lift_exists
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_estimate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ τ, ∃ hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C)), Function.Injective hb ∧ LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) ∧ (stdLat RC _).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).omHT τ ∧ (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ ∧ (∀ b' c'', (b', c'') ∈ ((chartD e b pq sc w P i).bc RC).Del τ ↔ (algebraMap O C w) • b' ∈ stdLat RC _ ∧ c'' - (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) b' ∈ ((chartD e b pq sc w P i).bc RC).omHT τ) ∧ (∀ a b', (a, b') ∈ ((chartD e b pq sc w P i).bc RC).Gam τ ↔ (algebraMap O C w) • a ∈ ((chartD e b pq sc w P i).bc RC).W τ ∧ b' - hb a ∈ stdLat RC _) ∧ ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.htLift
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  first | exact @PositivityTheory.Xgn.test_group_point_exists | exact PositivityTheory.Xgn.test_group_point_exists
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_curve_model_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

theorem af_le_stdLat {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) {F : Type} [Zero F] [One F]
    [DecidableEq F] [Fintype F] (h01 : (0 : F) ≠ 1) {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (p : ℕ)
    (hM : D.M ≤ stdLat RC _) (χ : F → C) (h0 : χ 0 = 0) (h1 : χ 1 = 1) : D.af RC p χ ≤ stdLat RC _ := by
  intro l hl
  have hl1 : D.l1 RC p ≤ stdLat RC _ := by
    refine sup_le hM ?_
    rintro _ ⟨x, hx, rfl⟩
    intro a _
    have : x a ∈ RC := hx a (Set.mem_univ a)
    have h2 : (p : C) * x a ∈ RC := by
      have := RC.mul_mem (natCast_mem RC p) this
      simpa using this
    simpa using h2
  have h3 := hl1 hl
  intro k _
  have h4 : (linMap n χ l) (Pi.single k 1) ∈ RC := h3 _ (Set.mem_univ _)
  have h5 : (linMap n χ l) (Pi.single k 1) = l k := by
    simp only [linMap, Fintype.linearCombination_apply, LinearMap.coe_mk]
    rw [Finset.sum_apply, Finset.sum_eq_single k]
    · simp [h1]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj, h0]
    · simp
  rw [h5] at h4
  exact h4

set_option maxHeartbeats 4000000 in
theorem testFacts (hF : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate) (hQ : GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement) (hZ : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement) (hH : GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement) (hOC : GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) →  ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hAr hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _ hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σ hOrb hSec G c' hc' P i hseq hBase C _ _ _ _ RC hT χ hχ
  classical
  obtain ⟨hAC, ⟨v, hv, hvp⟩, hcomp, hRC⟩ := id hT
  haveI := hAC
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  haveI : CharZero C := (RingHom.charZero_iff (algebraMap Ω C).injective).1 inferInstance
  haveI : Finite (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by
    simp [Ideal.span_singleton_eq_bot, (Fact.out : p.Prime).ne_zero])
  letI : Fintype (TestPt.NAdd E (D.p + D.q) p) := Fintype.ofFinite _
  have hInt : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun {x} h => ⟨⟨x, (hv _).2 h⟩, rfl⟩⟩
  have hw : algebraMap O C w = algebraMap Ω C (algebraMap O Ω w) := IsScalarTower.algebraMap_apply O Ω C w
  obtain ⟨hO1, -⟩ : (∃ u : O, IsUnit u ∧ w ^ (p - 1) = u * (p : O)) ∧ True := ⟨hOrb.2.2.2.2.2.2.1.2.1, trivial⟩
  have hp0 : (p : O) ≠ 0 := hOrb.2.2.2.2.2.2.1.1

  obtain ⟨u, hu, hup⟩ := hO1
  have hp1 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpΩ : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpC : (p : C) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  have hcd : CharData (CR O y c') p (algebraMap O Ω w)
      (fun (_ : Sg) (a : F) => if a = 0 then (0 : Ω) else 1) := by
    refine ⟨hpΩ, Subalgebra.algebraMap_mem _ w, ?_, h01, fun τ => ⟨by simp, by simp, fun a => ?_⟩⟩
    · obtain ⟨u', hu'⟩ := hu.exists_left_inv
      refine ⟨algebraMap O Ω (u' * w ^ (p - 2)), Subalgebra.algebraMap_mem _ _, ?_⟩
      have e1 : w ^ (p - 1) = w ^ (p - 2) * w := by
        rw [← pow_succ]; congr 1; omega
      have e2 : (p : O) = u' * w ^ (p - 2) * w := by
        rw [_root_.mul_assoc, ← e1, hup, ← _root_.mul_assoc, hu', _root_.one_mul]
      have := congrArg (algebraMap O Ω) e2
      simpa [map_mul] using this
    · show (if a = 0 then (0 : Ω) else 1) ∈ CR O y c'
      by_cases ha : a = 0
      · simp only [ha, if_true]; exact zero_mem _
      · simp only [ha, if_false]; exact one_mem _
  have hBase' : ((chartD e b pq sc w P i).bc RC).Base RC p (algebraMap O C w) := by
    rw [hw]
    exact (GlobalTheory.T.lattice_base_change_larger_ring_holds (chartD e b pq sc w P i) (CR O y c') p (algebraMap O Ω w) _ hcd hBase C RC hRC).2
  have hw0 : algebraMap O C w ≠ 0 := by
    intro h0
    have e1 := congrArg (algebraMap O C) hup
    rw [map_pow, h0, zero_pow (by omega), map_mul, map_natCast] at e1
    exact mul_ne_zero (hu.map (algebraMap O C)).ne_zero hpC e1.symm
  obtain ⟨AA, AW, hAA, hAW, hM, hstab, hFS⟩ := GlobalTheory.T.arith_variety_prime_global_relay E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ
  obtain ⟨hAb, hTi⟩ := GlobalTheory.T.arith_variety_model_hodge_relay hH hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp
  obtain ⟨σ', ee, hfund, hχσ, hσφ⟩ := GlobalTheory.T.arith_variety_prime_hodge_total E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ
  have hptors : ∀ x : TestPt.NAdd E (D.p + D.q) p, p • x = 0 := by
    intro x
    ext k
    have : ((p : ℕ) : 𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    simp [nsmul_eq_mul, this]
  have hsec : ∀ x : Fin (D.p + D.q) → F, TestPt.fromNAdd pq (TestPt.toNAdd sc x) = x := by
    intro x
    ext k
    exact hSec.1 (x k)
  have hFlag : GlobalTheory.CompanionTheory.Ar.GR.FlagConcl v p AW.carrier (Pi.basisFun F (Fin (D.p + D.q))) σ' := by
    have h1 := GlobalTheory.T.abelian_factor_tight_field_action (GlobalTheory.T.quotient_zarhin_hodge_tate_subquotient hQ hZ hH) p C v RC hInt hvp hcomp (TestPt.NAdd E (D.p + D.q) p) AA hptors
      (by rw [hAA]; exact hAb) (by rw [hAA]; exact hTi) F (Fin (D.p + D.q) → F) (TestPt.toNAdd sc) (TestPt.fromNAdd pq)
      hsec hstab (by rw [hAA]; rw [hAW] at hFS; exact hFS) (D.p + D.q) (Pi.basisFun F (Fin (D.p + D.q))) σ' hfund
    rw [hAW]
    rw [hAA] at h1
    exact h1
  have hTh := GlobalTheory.T.chartD_th_sqIdeal_mem_and_smul_mem_and_eig_mem_sqIdeal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ σ' ee hχσ
  have hTh' : ∀ τ, (∀ g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal AW.carrier), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ (∀ (a : F) g m, (g, m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → ((fun x => g (a • x)), (fun (τ : Sg) (a : F) => χ τ a) τ a • m) ∈ ((chartD e b pq sc w P i).bc RC).Th τ) ∧ ∀ g ∈ GlobalTheory.CompanionTheory.Ar.GR.eig AW.carrier (σ' ^ p ^ ee τ), (g, 0) ∈ ((chartD e b pq sc w P i).bc RC).Th τ → g ∈ ReciprocityTheory.PGsh.Up.sqIdeal (ReciprocityTheory.PGsh.L2.augIdeal AW.carrier) := by
    rw [hAW]
    exact hTh
  have hleaf := GlobalTheory.T.arith_variety_model_prime_total hZ hH E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp hAb
  have haf : ∀ τ, ((chartD e b pq sc w P i).bc RC).af RC p (fun a => χ τ a) ≤ stdLat RC _ := fun τ =>
    af_le_stdLat RC h01 _ p hBase'.M_le _ (map_zero (χ τ)) (map_one (χ τ))
  have hseq' : ∀ τ, ((chartD e b pq sc w P i).bc RC).imH RC p τ (fun a => χ τ a) = ((chartD e b pq sc w P i).bc RC).om τ ∧
      ((chartD e b pq sc w P i).bc RC).kerH RC p τ (fun a => χ τ a) = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
    intro τ
    obtain ⟨hbb, h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.T.arith_variety_prime_hodge_estimate E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ τ
    obtain ⟨g1, g2⟩ := GlobalTheory.T.ordinary_curve_model_relay hF hQ hZ hH hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hAr hpq p hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σ hOrb hSec G c' hc' P i hseq hBase C RC hT χ hχ v hv hvp τ hbb h1 h2 h4 h7
    exact GlobalTheory.T.hodge_kernel_image_lattice RC p ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) τ hw0 (hleaf τ) (haf τ)
      _ hbb h1 h2 h3 h4 g1 g2 h5 h6
  exact ⟨hleaf, fun τ => (hseq' τ).1, fun τ => (hseq' τ).2,
    GlobalTheory.CompanionTheory.Ar.Num.PtDx.main RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh',
    GlobalTheory.CompanionTheory.Ar.Num.stepGraph_snd_eq_kk RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh',
    GlobalTheory.CompanionTheory.Ar.Num.PtInj.kernel_stepGraph RC v hv p hvp ((chartD e b pq sc w P i).bc RC) (algebraMap O C w) (fun (τ : Sg) (a : F) => χ τ a) φ' hBase' AW hM hFS σ' hfund hFlag ee hχσ hσφ hTh'⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinary_curve_hodge_prime : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ((chartD e b pq sc w P i).bc RC).Facts RC p (algebraMap O C w) (fun τ a => χ τ a) φ' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.testFacts
end

section
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem gamDel_of_seqHyp {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (w : Ω) (hw : w ∈ R)
    (hw0 : w ≠ 0) {r s n : ℕ} (W : AddSubgroup (Fin r → Ω)) (om : AddSubgroup (Fin s → Ω))
    (hW : ∀ a ∈ R, ∀ v ∈ W, a • v ∈ W) (hom : ∀ a ∈ R, ∀ v ∈ om, a • v ∈ om)
    (i : (Fin r → Ω) →ₗ[Ω] (Fin n → Ω)) (q : (Fin n → Ω) →ₗ[Ω] (Fin s → Ω)) (h : SeqHyp R w W om i q) :
    (∀ a ∈ R, (∀ v ∈ gamLat R w W i, a • v ∈ gamLat R w W i) ∧ ∀ v ∈ delLat R w om q, a • v ∈ delLat R w om q) ∧
    ((∀ a, (∃ b, (a, b) ∈ gamLat R w W i) ↔ w • a ∈ W) ∧ (∀ b, (0, b) ∈ gamLat R w W i ↔ b ∈ stdLat R (Fin n)) ∧
      ∀ a, (a, 0) ∈ gamLat R w W i ↔ a ∈ W) ∧
    ((∀ b, (∃ c, (b, c) ∈ delLat R w om q) ↔ w • b ∈ stdLat R (Fin n)) ∧
      (∀ c, (∃ b, (b, c) ∈ delLat R w om q) ↔ w • c ∈ om) ∧ (∀ c, (0, c) ∈ delLat R w om q ↔ c ∈ om) ∧
      ∀ b, (b, 0) ∈ delLat R w om q ↔ ∃ a, (a, b) ∈ gamLat R w W i) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨Gam, Del, hG, hD, hst, hg, hd⟩ := GlobalTheory.T.short_exact_standard_lattice o Ω R w hw hw0 r s n W om hW hom i q h1 h2 h3 h4 h5
  have eG : Gam = gamLat R w W i := by
    ext ⟨a, b⟩
    exact hG a b
  have eD : Del = delLat R w om q := by
    ext ⟨a, b⟩
    exact hD a b
  subst eG eD
  exact ⟨hst, hg, hd⟩

end GlobalTheory.CompanionTheory.Ar.Num.FamEx

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in

theorem familyExistsPos_holds : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos := by
  intro hF hQ hZ hH hOrd E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d ha hpq b hb p hpS hfree h2 hdisc φ hφ A _ _ _ m _ hm O _ _ _ _ _ _ _ t₀
  haveI : Fact p.Prime := ⟨𝔐.S_prime p hpS⟩
  obtain ⟨Sg, _, e, φ', F, _, _, _, pq, sc, w, σ, hO, hS⟩ :=
    GlobalTheory.T.arith_variety_hodge_prime_bound E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc φ hφ A m hm O t₀
  obtain ⟨G⟩ := GlobalTheory.T.arith_variety_hodge_prime_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc
  have hP := GlobalTheory.T.arith_variety_hodge_prime_height E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc A m hm O G
  let P : ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → ChartPack G O c' := fun c' h => (hP c' h).some
  have hcp : HT.IsCp p (algebraMap O Ω w) := hO.2.2.2.2.2.2.2
  have hL := GlobalTheory.T.arith_variety_model_prime_bound hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb A m hm O w hcp
  have hQs := fun (c' : ∀ k, J k) (h : mseg y c' ≠ 0) (τ : Sg) =>
    GlobalTheory.T.arith_variety_model_prime_degree hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb A m hm O w hcp G c' h (P c' h) (e τ)
  classical
  let i : ∀ (c' : ∀ k, J k) (τ : Sg), (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω) :=
    fun c' τ => if h : mseg y c' ≠ 0 then (hQs c' h τ).choose else 0
  have hi : ∀ (c' : ∀ k, J k) (h : mseg y c' ≠ 0) (τ : Sg), SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i c' τ) (qMap (P c' h) (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq (P c' h) σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i c' τ) := fun c' h τ => by
    have heq : i c' τ = (hQs c' h τ).choose := dif_pos h
    rw [heq]
    exact (hQs c' h τ).choose_spec
  have hw0 : algebraMap O Ω w ≠ 0 := by
    have h3 := hcp
    unfold HT.IsCp at h3
    rw [if_neg h2] at h3
    obtain ⟨ζ, hζ, e1⟩ := h3
    rw [e1]
    exact hζ.sub_one_ne_zero (Fact.out : p.Prime).one_lt
  have hwR : ∀ c' : ∀ k, J k, algebraMap O Ω w ∈ CR O y c' := fun c' => Subalgebra.algebraMap_mem _ w
  have hBase : ∀ (c' : ∀ k, J k) (h : mseg y c' ≠ 0),
      (chartD e b pq sc w (P c' h) (i c')).Base (CR O y c') p (algebraMap O Ω w) := by
    intro c' h
    obtain ⟨hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.T.arith_variety_hodge_prime_count E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb φ hφ A m hm O t₀ Sg e φ' F pq sc w σ hO hS G c' h (P c' h) (i c')
    have hG := fun τ : Sg => gamDel_of_seqHyp (CR O y c') (algebraMap O Ω w) (hwR c') hw0
      (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c')
      (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c'))
      ((hL (e τ)).2.2.2.2 c' h).2.1.1 ((hL (e τ).swap).2.2.2.2 c' h).2.2.2.1.1 (i c' τ) (qMap (P c' h) (b (e τ).swap)) (hi c' h τ).1
    exact
      { freeM := hf1
        M_le := hf2
        le_M := hf3
        one_mem := hf4
        free := fun τ => ⟨((hL (e τ)).2.2.2.2 c' h).1, ((hL (e τ)).2.2.2.2 c' h).2.1,
          ((hL (e τ).swap).2.2.2.2 c' h).2.2.1, ((hL (e τ).swap).2.2.2.2 c' h).2.2.2.1⟩
        incl := fun τ => ⟨((hL (e τ)).2.2.2.2 c' h).2.2.2.2.1, ((hL (e τ)).2.2.2.2 c' h).2.2.2.2.2.1,
          ((hL (e τ).swap).2.2.2.2 c' h).2.2.2.2.2.2.1, ((hL (e τ).swap).2.2.2.2 c' h).2.2.2.2.2.2.2⟩
        stable := fun τ a ha => ⟨((hG τ).1 a ha).1, ((hG τ).1 a ha).2, (hf5 τ).1 a ha⟩
        gam := fun τ => (hG τ).2.1
        del := fun τ => (hG τ).2.2
        th := fun τ => (hf5 τ).2 }
  have hFun := GlobalTheory.T.arith_variety_hodge_prime_total E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb φ hφ A m hm O t₀ Sg e φ' F pq sc w σ hO hS G P i
  have hSf := GlobalTheory.T.arith_variety_model_prime_height hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb φ hφ A m hm O t₀ Sg e φ' F pq sc w σ hO hS G P i hi
  have hpos := fun c' h => famD_pos (O := O) e b pq sc w P i c' h
  refine ⟨Sg, inferInstance, e, φ', F, inferInstance, inferInstance, inferInstance, w, σ, famD e b pq sc w P i, hO.1, hO.2.2.1, ?_, ?_⟩
  · refine ⟨hFun.1, fun τ => ⟨?_, ?_, ?_, ?_, (hSf τ).1, (hSf τ).2, hFun.2 τ⟩, hO.2.2.2.2.2.2.1, ?_, ?_⟩
    · exact isLatFamily_congr (fun c' h => by rw [hpos c' h]; rfl) (hL (e τ)).1
    · exact isLatFamily_congr (fun c' h => by rw [hpos c' h]; rfl) (hL (e τ)).2.1
    · exact isLatFamily_congr (fun c' h => by rw [hpos c' h]; rfl) (hL (e τ).swap).2.2.1
    · exact isLatFamily_congr (fun c' h => by rw [hpos c' h]; rfl) (hL (e τ).swap).2.2.2.1
    · intro c' h
      rw [hpos c' h]
      exact hBase c' h
    · intro c' h C _ _ _ _ RC hRC χ hχ
      rw [hpos c' h]
      exact GlobalTheory.T.ordinary_curve_hodge_prime hF hQ hZ hH hOrd E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha hpq p hpS hfree h2 hdisc b hb φ hφ A m hm O t₀ Sg e φ' F pq sc w σ hO hS G c' h (P c' h) (i c') (hi c' h) (hBase c' h) C RC hRC χ hχ
  · intro c' h τ
    rw [hpos c' h]
    exact ⟨rfl, rfl, rfl, rfl⟩
end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_pos_of_hodge_tate_inputs : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → GlobalTheory.CompanionTheory.Ar.Num.FamilyExistsPos := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds
end
