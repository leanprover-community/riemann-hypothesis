import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHTFrameCpAndNonempty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SupCLeISupGeneric
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.VVAlgebraMapNonneg

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

open NumberField IsDedekindDomain TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt GlobalTheory.FlagTan

theorem finite_of_finRes {T₀ T : CDVR} (hT : T.FinRes) (g : T₀.V →+* T.V) (hg : Function.Injective g)
    [IsLocalHom g] : g.Finite := by
  letI := g.toAlgebra
  haveI : Finite (T.V ⧸ maximalIdeal T.V) := hT
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  refine GlobalTheory.finite_of_forall_prime_mem (R := T₀.V) (B := T.V) hp.ne_zero (fun P hP h0 => ?_) ?_ ?_
  · rw [eq_maximalIdeal (hP.isMaximal h0)]
    exact hp.not_isUnit
  · exact fun h => IsDiscreteValuationRing.not_a_field _ ((Ideal.map_eq_bot_iff_of_injective hg).1 h)
  · exact ne_top_of_le_ne_top (maximalIdeal.isMaximal T.V).ne_top (map_maximalIdeal_le g)


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [NumberField K] [Algebra c.F K] {y : FrPt Xo c K}
  {v : FinitePlace K}

theorem FinFr.exists_baseChange (F : FinFr y v) {W : CDVR} (i : F.T.Fr →+* W.Fr) {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV W.V (i x) = (r : ℤ) * vV F.T.V x) (io : c.F →+* W.Fr) (φ : CoefHom c io K)
    (hφ : ∀ a, i (F.φ a) = φ a) : ∃ z : IntFr Xo c W io, letI := io.toAlgebra
      Reframes φ y (fun k => Units.map (i : F.T.Fr →* W.Fr) (F.t k)) z.1 := by
  obtain rfl : i.comp F.io = io := RingHom.ext fun a => by
    letI := io.toAlgebra
    exact (congrArg i (F.φ.commutes a).symm).trans ((hφ _).trans (φ.commutes a))
  letI := (i.comp F.io).toAlgebra
  obtain ⟨z, ψ, hψ, hz⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c F.T W F.io F.pt i r hr
    fun a _ => hi a
  obtain rfl : ψ = ⟨i, fun _ => rfl⟩ := AlgHom.ext (RingHom.congr_fun hψ)
  obtain ⟨w, h₁, h₂⟩ := F.tri
  obtain ⟨w', hw'⟩ := exists_frMap (⟨i, fun _ => rfl⟩ : F.T.Fr →ₐ[c.F] W.Fr) w
  exact ⟨z, w', frMap_comp h₁ hw' hφ, GlobalTheory.SupGeneric.frBor_of_frMap _ h₂ hw' hz⟩





end GlobalTheory.CompHS
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_ext_of_integral {A B O C : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing O] [Field C] [IsAlgClosed C] [Algebra O C] (v : Valuation C ℝ≥0) (hv : v.Integers O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral) (j0 : A →+* O)
    (hj0 : Function.Injective ((algebraMap O C).comp j0)) :
    ∃ j1 : B →+* O, j1.comp φ = j0 ∧ Function.Injective ((algebraMap O C).comp j1) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra A O := j0.toAlgebra
  letI : Algebra A C := ((algebraMap O C).comp j0).toAlgebra
  haveI : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hφ
  haveI : FaithfulSMul A C := (faithfulSMul_iff_algebraMap_injective A C).2 hj0
  let ψ : B →ₐ[A] C := IsAlgClosed.lift
  have hmem : ∀ b : B, ∃ o : O, algebraMap O C o = ψ b := fun b => by
    have h1 : IsIntegral A (ψ b) := (Algebra.IsIntegral.isIntegral (R := A) b).map ψ
    have h2 : IsIntegral O (ψ b) := h1.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral h2)
  choose f hf using hmem
  have hinj := hv.hom_inj
  let j1 : B →+* O :=
    { toFun := f
      map_one' := hinj (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul, hf, hf, hf, map_mul])
      map_zero' := hinj (by rw [hf, map_zero, map_zero])
      map_add' := fun x y => hinj (by rw [map_add, hf, hf, hf, map_add]) }
  have hcomp : j1.comp φ = j0 := by
    ext a
    apply hinj
    change algebraMap O C (f (algebraMap A B a)) = algebraMap A C a
    rw [hf, ψ.commutes]
  refine ⟨j1, hcomp, ?_⟩
  have hψ : (algebraMap O C).comp j1 = ψ.toRingHom := RingHom.ext fun b => hf b
  rw [hψ, RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := A) ?_
  rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  have : ψ.toRingHom.comp (algebraMap A B) = algebraMap A C := ψ.comp_algebraMap
  rw [this]
  exact hj0

theorem exSt_of_cmpSt : CmpSt → ExSt := by
  intro hC E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle hpq _hA _hgood Z la p _ Xw hcov yb hyb
  obtain ⟨⟨T, kO, yT, hfin, hkO, hyT⟩, hXw⟩ := hyb
  obtain ⟨hover, -, -, -, hjr, -, -, -, -⟩ := hcov
  have hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := (PadicComplexInt.integers p).hom_inj

  have hgXw : Set.range (spMap (algebraMap T.V T.Fr) ≫ yT) ⊆ (Xw : Set Y.X) := by
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr) := Subsingleton.elim (α := PrimeSpectrum T.Fr) _ _
    have h1 := bot_map (IsFractionRing.injective T.V T.Fr) yT
    have h2 := bot_map (φ := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) (hiO.comp hkO) yT
    have h3 : (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]) ∈ (Xw : Set Y.X) :=
      hXw ⟨_, rfl⟩
    rw [← hyT, sp_sp, h2] at h3
    rw [h1]
    exact h3
  obtain ⟨yyT, hyyT⟩ := GlobalTheory.LN.ArcClause.exists_lift (c'.V W) Y _ (hgXw.trans hjr)
  obtain ⟨io', hio'⟩ : ∃ io' : c'.F →+* T.Fr, yyT ≫ pullback.snd _ _ = spMap io' :=
    ⟨(Spec.preimage (yyT ≫ pullback.snd _ _)).hom, (Spec.map_preimage (yyT ≫ pullback.snd _ _)).symm⟩
  let io : c.F →+* T.Fr := io'.comp (IntermediateField.inclusion hle).toRingHom
  have hrs : yyT ≫ r ≫ pullback.snd _ _ = spMap io := by
    rw [hover, ← Category.assoc, hio', spMap_spMap]
  let x : Sp T.Fr ⟶ Xo.X := yyT ≫ r ≫ pullback.fst _ _
  have hx : (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) := by
    letI := io.toAlgebra
    show (yyT ≫ r ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc r, ← Category.assoc yyT, hrs, sOf,
      spMap_spMap]
  obtain ⟨T', i, rr, hrr, hv, hfin', y₀, hy₀⟩ := GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c hpq T io hfin x hx
  obtain ⟨φ, hφ, hloc⟩ := GlobalTheory.GoodChartExt.exists_local_restrict T T' i rr hrr hv
  have hφi : Function.Injective φ := by
    intro a b h
    apply i.injective.comp (IsFractionRing.injective T.V T.Fr)
    have ha := RingHom.congr_fun hφ a
    have hb := RingHom.congr_fun hφ b
    simp only [RingHom.comp_apply] at ha hb
    simp only [Function.comp_apply, ← ha, ← hb, h]
  have hfinφ : φ.Finite := GlobalTheory.CompHS.finite_of_finRes hfin' φ hφi
  obtain ⟨kO', hkO', hinj'⟩ := exists_ext_of_integral (Valued.v : Valuation ℂ_[p] ℝ≥0) (PadicComplexInt.integers p)
    φ hφi hfinφ.to_isIntegral kO (hiO.comp hkO)
  let k : T'.Fr →+* ℂ_[p] := IsFractionRing.lift hinj'
  have hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k (algebraMap T'.V T'.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap hinj' a).symm
  letI := (i.comp io).toAlgebra
  letI : Algebra c.F ℂ_[p] := (k.comp (i.comp io)).toAlgebra
  letI := H.starRing
  let kA : T'.Fr →ₐ[c.F] ℂ_[p] := { k with commutes' := fun _ => rfl }
  obtain ⟨y, hy⟩ := GlobalTheory.CompHt.exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p])
    (fun _ => rfl) (PadicComplexInt.integers p) y₀ hfin' kA kO' hk
  have hcomm : spMap (algebraMap T'.V T'.Fr) ≫ (spMap φ ≫ yT) = (spMap i ≫ yyT) ≫ Y.j := by
    rw [sp_sp, hφ, ← sp_sp, Category.assoc, hyyT]
  have hpt : (spMap i ≫ yyT) ≫ r = spMap (RingHom.id T'.Fr) ≫ GlobalTheory.AllWt.ptF y₀.1 := by
    rw [show spMap (RingHom.id T'.Fr) = 𝟙 _ from Spec.map_id _, Category.id_comp]
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hy₀, Category.assoc, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, Category.assoc, hrs, spMap_spMap]
  obtain ⟨P, π, ψ, h⟩ := hC E H Dw l l' Xo Xo' c c' W Y r ν hle hover p T' T' (RingHom.id _) (RingHom.id _)
    (fun _ => rfl) (i.comp io) y₀ kA y hy k kO' hk (fun _ => rfl) (spMap φ ≫ yT) (spMap i ≫ yyT) hcomm hpt
  rw [sp_sp, hkO', hyT] at h
  exact ⟨_, _, y, P, π, ψ, h⟩

end GlobalTheory.FlatModel

end
end
