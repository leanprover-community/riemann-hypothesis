module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersPropertiesStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateConstantDividesPSqStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralPointCompleteValuedFieldStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelRankEqGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoTorsionTowerStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionTowerWeilPairingStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatTest

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.TestPts

theorem isProper_snd_comp {G S Y Z : Scheme.{0}} (f : G ⟶ S) (h : Y ⟶ S) (g : Z ⟶ Y)
    [IsProper (Limits.pullback.snd f h)] : IsProper (Limits.pullback.snd f (g ≫ h)) := by
  have hc : Limits.pullback.fst f (g ≫ h) ≫ f = (Limits.pullback.snd f (g ≫ h) ≫ g) ≫ h := by
    rw [Limits.pullback.condition, Category.assoc]
  have hp : IsPullback (Limits.pullback.lift _ _ hc) (Limits.pullback.snd f (g ≫ h))
      (Limits.pullback.snd f h) g := by
    refine IsPullback.of_right (h₁₂ := Limits.pullback.fst f h) (v₁₃ := f) (h₂₂ := h) ?_
      (Limits.pullback.lift_snd _ _ hc) (IsPullback.of_hasPullback f h)
    rw [Limits.pullback.lift_fst]
    exact IsPullback.of_hasPullback f (g ≫ h)
  exact MorphismProperty.of_isPullback (P := @IsProper) hp inferInstance

theorem exists_unit_of_pow {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    (u : (FractionRing O)ˣ) (m : ℕ) (hm : 0 < m) (h : u ^ m = 1) :
    ∃ w : Oˣ, algebraMap O (FractionRing O) w = u := by
  have h1 : IsIntegral O (u : FractionRing O) :=
    IsIntegral.of_pow hm (by rw [← Units.val_pow_eq_pow_val, h]; exact isIntegral_one)
  have h2 : IsIntegral O ((u⁻¹ : (FractionRing O)ˣ) : FractionRing O) :=
    IsIntegral.of_pow hm (by rw [← Units.val_pow_eq_pow_val, inv_pow, h]; simpa using isIntegral_one)
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have hab : a * b = 1 := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, ha, hb, map_one]; simp
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

theorem finite_levGrp (La : Type) [AddCommGroup La] [Module.Finite ℤ La] (p n : ℕ) (hp : 0 < p) :
    Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) x
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change ((p ^ n : ℕ) : ℤ) • (Submodule.Quotient.mk a : La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  exact this

theorem finrank_eq_rankAtStalk {A Q : Type} [CommRing A] [IsDomain A] [AddCommGroup Q] [Module A Q]
    [Module.Finite A Q] [Module.Projective A Q] (P : PrimeSpectrum A) :
    Module.finrank A Q = Module.rankAtStalk Q P := by
  have hbc := TensorProduct.isBaseChange A Q (FractionRing A)
  haveI := Module.finitePresentation_of_projective A Q
  rw [LieRank.finrank_eq_of_isBaseChange_fractionRing _ hbc,
    LieRank.finrank_of_isBaseChange _ hbc (IsLocalRing.closedPoint (FractionRing A))]
  exact (Module.isLocallyConstant_rankAtStalk (R := A) (M := Q)).apply_eq_of_preconnectedSpace _ _

theorem finrank_lie_eq (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom]
    (R O : Type) [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] [Algebra R O]
    (x : Sp R ⟶ S) (L L' : Type) [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module O L']
    (M : LieModel G x L) (M' : LieModel G (spMap (algebraMap R O) ≫ x) L') :
    Module.finrank O L' = Module.finrank R L := by
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective S G R x L M
  letI : Module R L' := Module.compHom L' (algebraMap R O)
  haveI : IsScalarTower R O L' := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj⟩ := LieRank.exists_lift G x M M'
  have hbc := GlobalTheory.T.lie_model_isBaseChange S G R O x L L' M M' j hj
  rw [← LinearEquiv.finrank_eq hbc.equiv,
    finrank_eq_rankAtStalk (IsLocalRing.closedPoint (FractionRing O) |> PrimeSpectrum.comap (algebraMap O (FractionRing O))),
    Module.rankAtStalk_baseChange]
  exact (finrank_eq_rankAtStalk _).symm

theorem reduces_at_point (hPt : PointHT) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω]
    [Module R Ω] [IsScalarTower R K Ω]
    (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La)
    (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S]
    (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left)
    (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L)
    (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω)
    (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R)
    (hc : IsHTChartOf Dc Γ₀ i M ρ j π ζ₀)
    (hπ : ∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k))
    (he : ∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n)))
    (hrank : 2 * Module.finrank R L = Module.finrank ℤ D.La)
    (hprop : IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)))
    (hκ : if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1)
    (C O : Type) [Field C] [IsAlgClosed C] [CharZero C] [CommRing O] [IsDomain O] [Algebra O C] [Algebra R O]
    (v : Valuation C NNReal) (hv : v.Integers O) (hp : v (p : C) < 1)
    (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (hinj : Function.Injective (algebraMap R O))
    [IsAlgClosed (FractionRing O)] [IsIntegrallyClosed O]
    (f : FractionRing R →+* FractionRing O)
    (hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r))
    (z : Sp (FractionRing O) ⟶ S) (hz : z = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x)
    (I : TateIso D (FractionRing O) (Over.mk z ⟶ t.G) (fun a g => g ≫ t.act.act a)
      (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)))
    (hI1 : (I.ζ (p ^ n) : FractionRing O) = f (algebraMap R _ (ζ₀ : R)))
    (hI2 : ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) :
    ∃ (L' : Type) (_ : AddCommGroup L') (_ : Module O L')
      (P : HTPoint C O (IsCMField.complexConj E).toRingEquiv (algebraMap R O κ) (D.p + D.q) (C ⊗[ℤ] D.La)
        (C ⊗[O] Module.Dual O L'))
      (io : Dc.om →ₛₗ[algebraMap R O] (C ⊗[O] Module.Dual O L')), Dc.ReducesTo (algebraMap R O) P io :=
  PositivityTheory.HtPt.Htat.TestPts.reduces_at_point hPt E H D p R K n Ω Dc u hu S t x Γ₀ i hi L M ρ hρ j hj π ζ₀ κ
    hc hπ he hrank hprop hκ C O v hv hp hO hinj f hf z hz I hI1 hI2

end GlobalTheory.CompanionTheory.Ar.HT.TestPts

namespace GlobalTheory.CompanionTheory.Ar.HT


open GlobalTheory.CompanionTheory.Ar.HT.TestPts in
theorem hasTestPoints_of_tate : PointHT → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (Dc : HTChart R K (IsCMField.complexConj E).toRingEquiv p n (D.p + D.q) Ω) (u : Fin (D.p + D.q) → D.La) (hu : IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (x : Sp R ⟶ S) (Γ₀ : QFGroup R (LevGrp D.La p n)) (i : Γ₀.G.left ⟶ t.G.left) (hi : Γ₀.IsTorsionAlong t.G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel t.G x L) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf t.act.act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin (D.p + D.q) → 𝓞 E) →* LevGrp D.La p n) (ζ₀ : Rˣ) (κ : R), IsHTChartOf Dc Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', Dc.e z z' = ((D.EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → 2 * Module.finrank R L = Module.finrank ℤ D.La → IsProper (Limits.pullback.snd t.G.hom ((BT.genPt R).hom ≫ x)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (f : FractionRing R →+* k), ∃ I : TateIso D k (Over.mk (spMap f ≫ (BT.genPt R).hom ≫ x) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)), (I.ζ (p ^ n) : k) = f (algebraMap R _ (ζ₀ : R)) ∧ ∀ a, (I.ev (p ^ n) a).left = spMap f ≫ (Γ₀.pt (lev p n a)).left ≫ i) → (if p = 2 then κ = 4 else ∃ ζ : R, IsPrimitiveRoot ζ p ∧ κ = ζ - 1) → Dc.HasTestPoints κ := by
  intro hPt E _ _ _ H D p _ R K _ _ _ _ _ _ _ _ n Ω _ _ _ _ Dc u hu S _ t x Γ₀ i hi L _ _ M ρ hρ j hj π ζ₀ κ hc hπ he hrank hprop hTate hκ 𝔮 hq hh hpq
  obtain ⟨C, O, iF, iAC, iCZ, iR, iD, iAl, v, φ, hv, hp, hO, hinj, hcent⟩ := GlobalTheory.T.integral_point_complete_valued_field R p 𝔮 hq hh hpq
  letI : Algebra R O := φ.toAlgebra
  obtain ⟨-, -, hIC, -, hAC, -⟩ := GlobalTheory.T.complete_integers_properties p C v O hv hp hO
  haveI := hAC
  haveI := hIC
  have hgk : Function.Injective ((algebraMap O (FractionRing O)).comp φ) :=
    (IsFractionRing.injective O _).comp hinj
  let f : FractionRing R →+* FractionRing O := IsFractionRing.lift hgk
  have hf : ∀ r, f (algebraMap R _ r) = algebraMap O _ (algebraMap R O r) :=
    fun r => IsFractionRing.lift_algebraMap hgk r
  obtain ⟨I, hI1, hI2⟩ := hTate (FractionRing O) f
  have hz : spMap f ≫ (BT.genPt R).hom ≫ x = (BT.genPt O).hom ≫ spMap (algebraMap R O) ≫ x := by
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simp only [Over.mk_hom, spMap]
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hf
  obtain ⟨L', iA', iM', P, io, hio⟩ := reduces_at_point hPt E H D p R K n Ω Dc u hu S t x Γ₀ i hi L M ρ hρ j hj π ζ₀ κ hc hπ he
    hrank hprop hκ C O v hv hp hO hinj f hf _ hz I hI1 hI2
  exact ⟨C, O, iF, iAC, iCZ, iR, iAl, v, φ, C ⊗[ℤ] D.La, C ⊗[O] Module.Dual O L', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, P, io, hv, hinj, hcent, hio⟩

end GlobalTheory.CompanionTheory.Ar.HT
