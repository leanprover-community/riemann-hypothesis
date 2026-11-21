import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfInducedOfInduced
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRefinementGenericDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementOfCoverAndModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricDifferenceLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCoversStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicNormNefPartialSums
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

namespace GlobalTheory.NefDeRhamAt

theorem nefAt_of_pull (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (hp : IsProjOver p) (hq : IsProjOver q) (π : Y ⟶ X) (hπ : π ≫ p = q) (hsurj : Function.Surjective π) (L : HermLB p)
    (r : ℕ) [Fact r.Prime]
    (hL : ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod r) ((L.pull π hπ).B.pull i) 1) :
    ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
  intro Z i _ _ _ hd
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : Surjective π := ⟨hsurj⟩
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := GlobalTheory.NefDescent.fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := GlobalTheory.NefDescent.red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := GlobalTheory.NefDescent.dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := GlobalTheory.NefDescent.isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod r) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod r) f
  have h1 := hL _ i' hd'
  have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have e1 : topSelfIntersection (ZMod r) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod r) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i')
      (fun _ => LB.isLB_pull hN f) fun _ => ?_
    show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))
    rw [← pull_comp, ← pull_comp, hcomm]
  have e2 : topSelfIntersection (ZMod r) ((L.B.pull i).pull f) 1 = interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) :=
    (interNumOn_const_eq_topSelf (k := ZMod r) (fun _ => rfl) hN 1).symm
  have e3 : interNumOn (ZMod r) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod r) f ![L.B.pull i] :=
    congrArg _ (funext fun j => by fin_cases j; rfl)
  have hproj : IsProjOver (strHom (ZMod r) Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod r) Z ≫ spMap (Int.castRingHom (ZMod r))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod r) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod r)))
    exact ProperCurve.isProjOver_of_isProper _ hd
  have e4 := GlobalTheory.T.intersection_number_finite_pushforward (ZMod r) Z _ f hproj hd hη (L.B.pull i) hN
  have e5 : interNum (ZMod r) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod r) (L.B.pull i) 1 := by
    rw [← e5, ← e4, ← e3, ← e2, ← e1]
    exact h1
  exact nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')

end GlobalTheory.NefDeRhamAt
end
end

section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_refinement_generic_degree : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (V' : Cover Y) (b : V'.X ⟶ V.X) (hb : b ≫ V.p = V'.p) (g : V'.G ⟶ V.G), V'.j ≫ b = g ≫ V.j → g ≫ V.π = V'.π → g (genericPoint V'.G) = genericPoint V.G → b (genericPoint V'.X) = genericPoint V.X ∧ b.residueDegree (genericPoint V'.X) * V.deg = V'.deg := by
  first | exact @GlobalTheory.CoverDeg.map_genericPoint_and_deg | exact GlobalTheory.CoverDeg.map_genericPoint_and_deg | (intros; apply GlobalTheory.CoverDeg.map_genericPoint_and_deg <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

section Induces

open GlobalTheory.Cartier GlobalTheory.CxPts ReciprocityTheory.ChartRestriction.G

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

theorem generatesAt_genAt_pow (D : Y.Dv) (k : ℕ) (x : Y.X) : (k • D).GeneratesAt x (genAt D x ^ k) := by
  have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn D x).nsmul k)
  rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this

theorem induces_twist_of_induced {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hA : A.Induced M L k cf) (V : Cover Y) (b : V.X ⟶ M.X) (hb : b ≫ M.p = V.p)
    (hj : V.j ≫ b = V.π ≫ M.j) : V.Induces (A.twist 0 (-cf)) (L.pull b hb) k := by
  haveI := M.ar.isIntegral
  obtain ⟨-, r, hr, h₁, h₂⟩ := hA
  obtain ⟨hη, e⟩ := V.φ_eq_fnMap
  set ψ := SmallSec.fnMap V.π hη with hψ
  have hφ : ∀ t, V.φ t = ψ t := fun t => by rw [e]
  have hg (x : Y.X) := generatesAt_genAt_pow A.D k x
  have hch : ∀ (i : ((L.pull b hb).B.pull V.j).ι), ∀ x ∈ ((L.pull b hb).B.pull V.j).U i,
      V.π x ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := by
    intro i x hx
    have h1 := Set.mem_iInter.1 (InducedPull.chart_le L.B b V.j i hx) PUnit.unit
    have h2 : (V.j ≫ b) x = M.j (V.π x) := by rw [hj]; rfl
    refine Set.mem_iInter.2 fun _ => ?_
    show M.j (V.π x) ∈ L.B.U _
    rw [← h2]
    exact h1
  let r' : ((L.pull b hb).B.pull V.j).ι → V.G.functionFieldˣ :=
    fun i => Units.map ψ.toMonoidHom (r fun _ => i PUnit.unit PUnit.unit)
  have hr' : ∀ i, (r' i : V.G.functionField) = ψ (r fun _ => i PUnit.unit PUnit.unit) := fun _ => rfl
  refine ⟨r', ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hmem : V.π (genericPoint V.G) ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit) := ⟨hch i _ hij.1, hch j _ hij.2⟩
    have h0 : genericPoint Y.X ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit) :=
      (genericPoint_specializes _).mem_open (TopologicalSpace.Opens.isOpen _) hmem
    have le : ((L.pull b hb).B.pull V.j).U i ⊓ ((L.pull b hb).B.pull V.j).U j ≤
        V.π ⁻¹ᵁ ((L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (L.B.pull M.j).U (fun _ => j PUnit.unit PUnit.unit)) :=
      fun x hx => ⟨hch i x hx.1, hch j x hx.2⟩
    rw [hr', hr', hr.isRatSec _ _ h0, map_mul, ← ProjSpace.fnOf_appLE V.π hη le h0 hij]
    congr 2
    have k1 := InducedPull.val_pull_g L.B M.j (fun _ => i PUnit.unit PUnit.unit) (fun _ => j PUnit.unit PUnit.unit)
      (InducedPull.inf_le _ _ _ _)
    have k2 := InducedPull.val_pull_g (L.B.pull b) V.j i j (InducedPull.inf_le _ _ _ _)
    have k3 := InducedPull.val_pull_g L.B b (i PUnit.unit) (j PUnit.unit) (InducedPull.inf_le _ _ _ _)
    refine (congrArg _ k1).trans (k2.trans ?_).symm
    refine (congrArg _ k3).trans ?_
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_apply_congr hj _ _ _ _ _
  · intro i x hx
    have hU := (hr.isEqn _ _ (hch i x hx)).generatesAt_iff.1 (hg (V.π x))
    rw [hr', hφ, ← map_pow, ← map_mul]
    exact unitAt_fnMap_of V.π hη hU
  · intro σ z y y' i e₁ e₂ hi
    change (Real.exp (-(2 * ((A.n : ℕ) : ℝ) * (A.ci (InfinitePlace.mk σ) + 0))) *
        C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ (k : ℕ) =
      ‖ratVal (V.φ (genAt A.D (under y)) ^ (k : ℕ) * (r' i : V.G.functionField)) z‖ ^ 2 *
        Real.exp (-((L.pull b hb).φ _).φ (i PUnit.unit) y')
    let y₀ := Points.PtsOver.map b hb _ y'
    have e₂' : y₀.1 = y.1 ≫ M.j := by
      show y'.1 ≫ b = y.1 ≫ M.j
      rw [e₂, e₁, Category.assoc, hj, Category.assoc]
    have hπ₀ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hi₀ : under y ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := hπ₀ ▸ hch i _ hi
    have H := h₁ σ y y₀ (fun _ => i PUnit.unit PUnit.unit) _ e₂' hi₀ (hg _).regularAt
    rw [C.pn_mPow Y σ A.D k _ _ y (generatesAt_genAt _ _)] at H
    have hU := (hr.isEqn _ _ hi₀).generatesAt_iff.1 (hg (under y))
    have hw : ((L.pull b hb).φ _).φ (i PUnit.unit) y' = (L.φ _).φ (i PUnit.unit PUnit.unit) y₀ :=
      (L.φ _).pull_φ b hb (i PUnit.unit) y'
    have hv : ratVal (V.φ (genAt A.D (under y)) ^ (k : ℕ) * (r' i : V.G.functionField)) z =
        ratVal (genAt A.D (under y) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) y := by
      have hU' : RegAt (V.π (under z)) (genAt A.D (under y) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) := by
        rw [hπ₀]; exact hU.regAt
      rw [hr', hφ, ← map_pow, ← map_mul, SmallSec.ratVal_eq_valAt z (ProjSpace.regAt_fnMap_of V.π hη hU'),
        SmallSec.ratVal_eq_valAt y hU.regAt, SmallSec.valAt_fnMap V.π hη z.1 hU', ← e₁]
    rw [hw, hv, ← H, add_zero, mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  · intro v e y z yt i e₁ e₂ hi
    change ((k : ℕ) : ℝ) * (A.lg v e y - ((A.n : ℕ) : ℝ) * (-cf) v) =
      Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) ^ (k : ℕ) * (r' i : V.G.functionField))))
    have e₂' : spMap e.O.subtype ≫ (yt ≫ b) = y.1 ≫ M.j := by
      rw [← Category.assoc, e₂, Category.assoc, hj, ← Category.assoc, e₁]
    have hi' : ⊤ ≤ (yt ≫ b) ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) :=
      fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have H := h₂ v e y (yt ≫ b) (fun _ => i PUnit.unit PUnit.unit) e₂' hi'
    have hmem : below y.1 ∈ (L.B.pull M.j).U (fun _ => i PUnit.unit PUnit.unit) := by
      have h1 : (y.1 ≫ M.j) (IsLocalRing.closedPoint _) ∈ L.B.U (i PUnit.unit PUnit.unit) := by
        rw [← e₂']
        exact hi' (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hU := (hr.isEqn _ _ hmem).generatesAt_iff.1 (hg (below y.1))
    have hπ₀ : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have hU' : RegAt (V.π (below z)) (genAt A.D (below y.1) ^ (k : ℕ) * (r fun _ => i PUnit.unit PUnit.unit : Y.Fn)) := by
      rw [hπ₀]; exact hU.regAt
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at H
    rw [hr', hφ, ← map_pow, ← map_mul, SmallSec.valAt_fnMap V.π hη z hU', e₁, Pi.neg_apply]
    linarith [H]

end Induces

theorem norms_pull_of_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → ∀ (V : Cover Y) (b : V.X ⟶ M.X) (hb : b ≫ M.p = V.p), V.j ≫ b = V.π ≫ M.j → Norms V (L.pull b hb) (fun x => genAt A.D x ^ (k : ℕ)) (fun σ y => ((k : ℕ) : ℝ) * lnAdl A σ y) (fun v e y => ((k : ℕ) : ℝ) * A.lg v e y + ((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ) * cf v) := by
  intro F _ _ C Y A M L k cf hA V b hb hj
  refine (norms_of_induces (induces_twist_of_induced hA V b hb hj)).congr (fun _ => rfl) (fun σ y => ?_) fun v e y => ?_
  · simp only [lnAdl, Adl.twist, Pi.add_apply, Pi.zero_apply, add_zero]
  · simp only [Adl.twist, Pi.neg_apply]
    ring

end GlobalTheory.CoverNorm
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_norms_pullback_power : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → ∀ (V : Cover Y) (b : V.X ⟶ M.X) (hb : b ≫ M.p = V.p), V.j ≫ b = V.π ≫ M.j → Norms V (L.pull b hb) (fun x => genAt A.D x ^ (k : ℕ)) (fun σ y => ((k : ℕ) : ℝ) * lnAdl A σ y) (fun v e y => ((k : ℕ) : ℝ) * A.lg v e y + ((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ) * cf v) := by
  first | exact @GlobalTheory.CoverNorm.norms_pull_of_induced | exact GlobalTheory.CoverNorm.norms_pull_of_induced | (intros; apply GlobalTheory.CoverNorm.norms_pull_of_induced <;> assumption)
end

section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem Cover.exists_valuationRing_point {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)
    {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G)
    (hz : z ≫ V.π = y.1) :
    ∃ yt : Sp e.O ⟶ V.X, spMap e.O.subtype ≫ yt = z ≫ V.j ∧
      ∀ U : V.X.Opens, yt (IsLocalRing.closedPoint e.O) ∈ U → ⊤ ≤ yt ⁻¹ᵁ U := by
  have hP : IsProper V.p := by
    obtain ⟨N, j, hj, he⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← he]; infer_instance
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O :=
    ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence V.p := by
    have h : UniversallyClosed V.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (z ≫ V.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) V.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, V.pb.w, ← Category.assoc, ← Category.assoc, hz, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := z ≫ V.j, i₂ := spMap φ, commSq := hsq }
  exact ⟨l.l, l.fac_left, fun U hU => ((IsLocalRing.closedPoint_mem_iff (R := e.O) (l.l ⁻¹ᵁ U)).1 hU).ge⟩

theorem Cover.finite_places_lg_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y) (L : HermLB V.p) (k : ℕ), k ≠ 0 → V.Induces A L k → ∀ y : AlgPt Y, {v : HeightOneSpectrum (𝓞 F) | ∃ e : TrueGeo.Ext v, A.lg v e y ≠ 0}.Finite := by
  intro F _ _ C Y V A L k hk0 hI y
  obtain ⟨r, -, -, -, hfin⟩ := hI
  obtain ⟨z, hz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_lift_pt V.π y.1
  have := V.ar.isNoetherian
  have hcov : (Set.univ : Set V.X) ⊆ ⋃ i, (L.B.U i : Set V.X) := by
    intro x _
    have hx : x ∈ (⨆ i, L.B.U i : V.X.Opens) := by rw [L.isLB.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun i => (L.B.U i : Set V.X))
    (fun i => (L.B.U i).isOpen) hcov
  let a : L.B.ι → AlgebraicClosure F := fun i =>
    valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r (fun _ => i) : V.G.functionField))
  have hB : ∀ i, {v : HeightOneSpectrum (𝓞 F) | a i ≠ 0 ∧ ∃ e : TrueGeo.Ext v, e.w (a i) ≠ 1}.Finite := by
    intro i
    by_cases h : a i = 0
    · simp [h]
    · exact (GlobalTheory.TrueGeo.finite_ext_ne_one F (a i) h).subset fun v hv => hv.2
  refine (S.finite_toSet.biUnion fun i _ => hB i).subset ?_
  rintro v ⟨e, he⟩
  obtain ⟨yt, hyt, hU⟩ := V.exists_valuationRing_point e y z hz
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.mp (hS (Set.mem_univ (yt (IsLocalRing.closedPoint e.O))))
  have h := hfin v e y z yt (fun _ => i) hz hyt (hU _ hi)
  by_contra h2
  have hlog : Real.log (e.w (a i)) = 0 := by
    by_cases h0 : a i = 0
    · simp [h0]
    · have : e.w (a i) = 1 := by
        by_contra hne
        exact h2 (Set.mem_iUnion₂.mpr ⟨i, hiS, h0, e, hne⟩)
      simp [this]
  have h3 : (k : ℝ) * A.lg v e y = 0 := h.trans hlog
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  exact he ((mul_eq_zero.mp h3).resolve_left hk)

end GlobalTheory.Mean4O
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNorm

theorem const_rat : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : HeightOneSpectrum (𝓞 F) → ℝ), Norms V L₁ f a l → Norms V L₂ f a (fun v e y => l v e y + c v) → ∀ v, ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * c v = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  intro F _ _ Y V L₁ L₂ f a l c h₁ h₂ v
  obtain ⟨e⟩ := (ExtConj.main F).1 v
  obtain ⟨y⟩ := ValGroup.nonempty_algPt Y
  obtain ⟨z, hz⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_lift_pt V.π y.1
  obtain ⟨yt, hyt, hU⟩ := V.exists_valuationRing_point e y z hz
  obtain ⟨r₁, -, hu₁, -, hf₁⟩ := h₁
  obtain ⟨r₂, -, hu₂, -, hf₂⟩ := h₂
  have chart (B : HermLB V.p) : ∃ i, yt (IsLocalRing.closedPoint e.O) ∈ B.B.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (B.isLB.cover.ge (Set.mem_univ _))
  obtain ⟨i, hi⟩ := chart L₁
  obtain ⟨i', hi'⟩ := chart L₂
  have k₁ := hf₁ v e y z yt (fun _ => i) hz hyt (hU _ hi)
  have k₂ := hf₂ v e y z yt (fun _ => i') hz hyt (hU _ hi')
  have hx : ∀ (B : HermLB V.p) (j : B.B.ι), yt (IsLocalRing.closedPoint e.O) ∈ B.B.U j →
      below z ∈ (B.B.pull V.j).U (fun _ => j) := by
    intro B j hj
    have h1 : (spMap e.O.subtype) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ yt ⁻¹ᵁ B.B.U j := hU _ hj trivial
    have h2 : (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ B.B.U j := by
      rw [← hyt]; exact h1
    exact Set.mem_iInter.2 fun _ => h2
  have hb : V.π (below z) = below y.1 := by rw [← hz]; rfl
  have n₁ := (Base.valAt_zpow z (hb ▸ hu₁ (fun _ => i) (below z) (hx L₁ i hi))).1
  have n₂ := (Base.valAt_zpow z (hb ▸ hu₂ (fun _ => i') (below z) (hx L₂ i' hi'))).1
  have key : c v = Real.log (e.w (TrueGeo.valAt z (V.φ (f (below y.1)) * ((r₂ fun _ => i' : V.G.functionFieldˣ) : V.G.functionField)) /
      TrueGeo.valAt z (V.φ (f (below y.1)) * ((r₁ fun _ => i : V.G.functionFieldˣ) : V.G.functionField)))) := by
    rw [map_div₀, Real.log_div (e.w.ne_zero n₂) (e.w.ne_zero n₁), ← k₁]
    simp only at k₂
    linarith
  obtain ⟨m, q, hm, hq⟩ := GlobalTheory.ExtValueGroup.log_w_rat F v e _ (div_ne_zero n₂ n₁)
  exact ⟨m, q, hm, by rw [key]; exact hq⟩
end CoverNorm
end GlobalTheory
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_shift_rational_multiple_log : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : HeightOneSpectrum (𝓞 F) → ℝ), Norms V L₁ f a l → Norms V L₂ f a (fun v e y => l v e y + c v) → ∀ v, ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * c v = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.CoverNorm.const_rat | exact GlobalTheory.CoverNorm.const_rat | (intros; apply GlobalTheory.CoverNorm.const_rat <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverNormConst

open GlobalTheory.Cartier GlobalTheory.CxPts

theorem norms_const_mul : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p)
    (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : F), c ≠ 0 → Norms V L f a l →
    Norms V L f (fun σ y => a σ y + Real.log ‖σ c‖)
      (fun v e y => l v e y + Real.log (NumberField.HeightOneSpectrum.adicAbv F v c)) := by
  intro F _ _ Y V L f a l c hc ⟨r, hr, hu, hinf, hfin⟩
  have hcu (x : V.G) := IndScale.unitAt_constFn (V.π ≫ Y.str) x hc
  let cu : V.G.functionFieldˣ := Units.mk0 (Cartier.constFn (V.π ≫ Y.str) c) (hcu (genericPoint V.G)).ne_zero
  have hcv : (cu : V.G.functionField) = Cartier.constFn (V.π ≫ Y.str) c := rfl
  refine ⟨fun i => r i * cu, fun i j h => ?_, fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · simp only [Units.val_mul]
    rw [hr i j h, mul_assoc]
  · rw [Units.val_mul, ← mul_assoc]
    exact (hu i x hx).mul (hcu x)
  · have hπ : V.π (under z) = under y := by
      show _ = y.1 _
      rw [e₁]
      rfl
    have hU := hu i _ hi
    rw [hπ] at hU
    beta_reduce
    rw [hinf σ z y y' i e₁ e₂ hi, Units.val_mul, ← mul_assoc, hcv,
      ratVal_mul hU.regAt (hcu _).regAt, IndScale.ratVal_constFn, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hU)) (norm_ne_zero_iff.2 ((map_ne_zero σ).2 hc))]
    ring
  · have hz : below z ∈ (L.B.pull V.j).U i := Set.mem_iInter.2 fun _ => by
      change (z ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ L.B.U (i PUnit.unit)
      rw [← e₂]
      exact hi (x := spMap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F))) trivial
    have hπ : V.π (below z) = below y.1 := by
      show _ = y.1 _
      rw [← e₁]
      rfl
    have hU := hu i _ hz
    rw [hπ] at hU
    have hy : z ≫ (V.π ≫ Y.str) = spMap (algebraMap F (AlgebraicClosure F)) := by
      rw [← Category.assoc, e₁]
      exact y.2
    beta_reduce
    rw [hfin v e y z yt i e₁ e₂ hi, Units.val_mul, ← mul_assoc, hcv,
      OfModel.valAt_mul _ hU.regAt (hcu _).regAt, IndScale.valAt_constFn _ _ z hy, map_mul, e.w_alg,
      Real.log_mul (e.w.ne_zero (IndScale.valAt_ne_zero _ hU)) (AbsoluteValue.ne_zero _ hc)]

end GlobalTheory.CoverNormConst

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norms_scale_by_constant : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L : HermLB V.p) (f : Y.X → Y.Fn) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (c : F), c ≠ 0 → Norms V L f a l → Norms V L f (fun σ y => a σ y + Real.log ‖σ c‖) (fun v e y => l v e y + Real.log (NumberField.HeightOneSpectrum.adicAbv F v c)) := by
  atlas_forward_decl GlobalTheory.CoverNormConst.norms_const_mul
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CoverNef

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem norms_shift {V : Cover Y} {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (t : (𝓞 F →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) :
    Norms V (L.shift t ht) f (fun σ y => a σ y - t (σ.comp (algebraMap (𝓞 F) F))) l := by
  obtain ⟨r, hr, hu, hc, hf⟩ := h
  refine ⟨r, hr, hu, fun σ z y y' i e₁ e₂ hi => ?_, hf⟩
  show a σ y - _ = _ - ((L.φ _).φ (i PUnit.unit) y' + 2 * t _) / 2
  rw [hc σ z y y' i e₁ e₂ hi]
  ring

theorem nefFib_of_norms {V : Cover Y} {L₁ L₂ : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} {c : HeightOneSpectrum (𝓞 F) → ℝ}
    (hc : (Function.support c).Finite) (h₁ : Norms V L₁ f a l) (h₂ : Norms V L₂ f a fun v e y => l v e y + c v)
    (hN : NefFib L₂) : NefFib L₁ := by
  obtain ⟨m, b, b', hb, hb', hm⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F c hc (GlobalTheory.T.norm_shift_rational_multiple_log F Y V L₁ L₂ f a l c h₁ h₂)
  have hb₀ : (algebraMap (𝓞 F) F b) ≠ 0 := by simpa using hb
  have hb₀' : (algebraMap (𝓞 F) F b') ≠ 0 := by simpa using hb'
  set q : F := algebraMap (𝓞 F) F b' / algebraMap (𝓞 F) F b with hq
  have hq₀ : q ≠ 0 := div_ne_zero hb₀' hb₀
  let t : (𝓞 F →+* ℂ) → ℝ := fun τ => Real.log ‖τ b'‖ - Real.log ‖τ b‖
  have ht : ∀ τ, t ((starRingEnd ℂ).comp τ) = t τ := fun τ => by simp [t]
  have N₁ := GlobalTheory.T.norms_tensor_power F Y V L₁ f a l m h₁
  have N₂ := norms_shift (GlobalTheory.T.norms_scale_by_constant F Y V _ _ _ _ q hq₀ (GlobalTheory.T.norms_tensor_power F Y V L₂ f a _ m h₂)) t ht
  have hI := GlobalTheory.T.isometric_of_same_norms F Y V _ _ _ _ _ N₁ (N₂.congr (fun _ => rfl) (fun σ y => ?_) (fun v e y => ?_))
  · have hp := GlobalTheory.T.nefFib_pow_iff' (𝓞 F) V.X V.p V.ar.isProjOver
    refine (hp L₁ m m.pos).1 ((GlobalTheory.TrueGeo.NefFibUniq.nefFib_iff_of_isometric hI).2 ?_)
    exact (GlobalTheory.TrueGeo.NefFibUniq.nefFib_shift _ _ _).2 ((hp L₂ m m.pos).2 hN)
  · have e₁ : (σ.comp (algebraMap (𝓞 F) F)) b' = σ (algebraMap (𝓞 F) F b') := rfl
    have e₂ : (σ.comp (algebraMap (𝓞 F) F)) b = σ (algebraMap (𝓞 F) F b) := rfl
    simp only [t, e₁, e₂, hq, map_div₀, norm_div]
    rw [Real.log_div (by simpa using hb₀') (by simpa using hb₀)]
    ring
  · have := hm v
    simp only [hq, map_div₀]
    rw [Real.log_div ((AbsoluteValue.pos_iff _).2 hb₀').ne' ((AbsoluteValue.pos_iff _).2 hb₀).ne']
    linear_combination this

end GlobalTheory.CoverNef

namespace GlobalTheory.CoverNef

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem surjective_of_cover {V V' : Cover Y} (a : V'.X ⟶ V.X) (ha : a ≫ V.p = V'.p) (g : V'.G ⟶ V.G)
    (hj : V'.j ≫ a = g ≫ V.j) (hπ : g ≫ V.π = V'.π) (hg : g (genericPoint V'.G) = genericPoint V.G) :
    Function.Surjective a := by
  obtain ⟨h₀, -⟩ := GlobalTheory.T.cover_refinement_generic_degree F Y V V' a ha g hj hπ hg
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : IsProper V'.p := CommonModel.isProper_of_isProjOver V'.ar.isProjOver
  have : IsProper (a ≫ V.p) := by rw [ha]; infer_instance
  have : IsProper a := IsProper.of_comp a V.p
  have : IsDominant a := ⟨Dense.mono (Set.singleton_subset_iff.2 ⟨_, h₀⟩)
    (dense_iff_closure_eq.2 ((genericPoint_spec V.X).trans Set.top_eq_univ))⟩
  exact (surjective_of_isDominant_of_isClosed_range a a.isClosedMap.isClosed_range).surj

theorem nefFib_of_norms_adl : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y), A.NefFib →
    ∀ (V : Cover Y) (L : HermLB V.p) (k : ℕ), 0 < k → Norms V L (fun x => genAt A.D x ^ k) (fun σ y => k * lnAdl A σ y)
      (fun v e y => k * A.lg v e y) → NefFib L := by
  intro _ F _ _ Y A ⟨M, L₀, k₀, cf, hI, hN⟩ V L k hk hL
  obtain ⟨V', a, g, b, ha, hb, hj, hπ, hg, hb'⟩ := GlobalTheory.Mean4O.CoverDom.exists_cover_dominating F Y V M
  have N₁ := GlobalTheory.T.norms_tensor_power F Y V' _ _ _ _ (k₀ : ℕ) (GlobalTheory.T.norms_pullback_along_cover F Y V V' a ha g hj hπ hg L _ _ _ hL)
  have N₂ := GlobalTheory.T.norms_tensor_power F Y V' _ _ _ _ k (GlobalTheory.T.cover_norms_pullback_power F (cxSt F) Y A M L₀ k₀ cf hI V' b hb hb')
  have hc : (Function.support fun v => (k : ℝ) * (k₀ : ℕ) * (A.n : ℕ) * cf v).Finite :=
    hI.1.subset (Function.support_mul_subset_right _ _)
  have hP := nefFib_of_norms hc N₁ (N₂.congr (fun x => by rw [← pow_mul, ← pow_mul, mul_comm])
    (fun σ y => by ring) (fun v e y => by ring))
    ((GlobalTheory.T.nefFib_pow_iff' (𝓞 F) V'.X V'.p V'.ar.isProjOver _ k hk).2
      (GlobalTheory.T.nefFib_pullback (𝓞 F) M.X V'.X M.p V'.p M.ar.isProjOver V'.ar.isProjOver b hb L₀ hN))
  exact GlobalTheory.T.nefFib_of_surjective_pullback (𝓞 F) V.X V'.X V.p V'.p V.ar.isProjOver V'.ar.isProjOver a ha
    (surjective_of_cover a ha g hj hπ hg) L ((GlobalTheory.T.nefFib_pow_iff' (𝓞 F) V'.X V'.p V'.ar.isProjOver _ _ k₀.pos).1 hP)

end GlobalTheory.CoverNef

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_fibre_of_norms_power : Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (A : Adl (cxSt F) Y), A.NefFib → ∀ (V : Cover Y) (L : HermLB V.p) (k : ℕ), 0 < k → Norms V L (fun x => genAt A.D x ^ k) (fun σ y => k * lnAdl A σ y) (fun v e y => k * A.lg v e y) → NefFib L := by
  atlas_forward_decl GlobalTheory.CoverNef.nefFib_of_norms_adl
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

namespace GlobalTheory.HtNefAbel

theorem sum_mul_le (N : ℕ) : ∀ (g n : Fin N → ℤ) (c : ℤ),
    (∀ i : ℕ, i ≤ N → ∑ a : Fin N, (if a.val < i then g a else 0) ≤ 0) → Antitone n → (∀ a, c ≤ n a) →
    ∑ a, n a * g a ≤ c * ∑ a, g a := by
  induction N with
  | zero => intro g n c _ _ _; simp
  | succ N ih =>
    intro g n c hS hn hc
    have h1 := ih (fun a => g a.castSucc) (fun a => n a.castSucc) (n (Fin.last N)) (fun i hi => by
        have := hS i (hi.trans (Nat.le_succ N))
        rw [Fin.sum_univ_castSucc, if_neg (by simpa using hi), add_zero] at this
        simpa using this)
      (fun a b hab => hn (by simpa using hab)) (fun a => hn (Fin.le_last _))
    have h2 : ∑ a, g a ≤ 0 := by
      have := hS (N + 1) le_rfl
      simpa only [Fin.is_lt, if_true] using this
    have h3 := mul_le_mul_of_nonpos_right (hc (Fin.last N)) h2
    rw [Fin.sum_univ_castSucc]
    refine le_trans ?_ h3
    rw [Fin.sum_univ_castSucc (f := g), mul_add]
    exact add_le_add h1 le_rfl

theorem sum_neg_mul_nonneg (T : Type) [Fintype T] (N : ℕ) (g : T × Fin N → ℤ)
    (h₁ : ∀ τ : T, ∀ i : ℕ, i < N → 0 ≤ ∑ x : T × Fin N, (if x.1 = τ ∧ x.2.val < i then -1 else 0 : ℤ) * g x)
    (h₂ : ∀ τ : T, 0 ≤ ∑ x : T × Fin N, (if x.1 = τ then 1 else 0 : ℤ) * g x)
    (h₃ : ∀ τ : T, 0 ≤ ∑ x : T × Fin N, (if x.1 = τ then -1 else 0 : ℤ) * g x)
    (n : T → Fin N → ℤ) (hn : ∀ τ, Antitone (n τ)) : 0 ≤ ∑ x : T × Fin N, -n x.1 x.2 * g x := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_nonneg fun τ _ => ?_
  have e₂ : 0 ≤ ∑ a, g (τ, a) := by
    have := h₂ τ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  have e₃ : ∑ a, g (τ, a) ≤ 0 := by
    have := h₃ τ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  obtain ⟨c, hc⟩ := (Set.finite_range (n τ)).bddBelow
  have := sum_mul_le N (fun a => g (τ, a)) (n τ) c (fun i hi => by
      rcases hi.lt_or_eq with hi | rfl
      · have := h₁ τ i hi
        rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
        rw [← neg_nonneg, ← Finset.sum_neg_distrib]
        refine this.trans_eq (Finset.sum_congr rfl fun a _ => ?_)
        by_cases h : a.val < i <;> simp [h]
      · simpa only [Fin.is_lt, if_true] using e₃) (hn τ) (fun a => hc ⟨a, rfl⟩)
  rw [le_antisymm e₃ e₂, mul_zero] at this
  simp only [neg_mul, Finset.sum_neg_distrib, neg_nonneg]
  exact this

theorem nefOver_comb_of_antitone : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ}, IsArithVar p d → ∀ (T : Type) [Fintype T] (N : ℕ) (M : T × Fin N → HermLB p) (l : ℕ), (∀ τ : T, ∀ i : ℕ, i < N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l) → (∀ τ : T, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l) → ∀ n : T → Fin N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  intro k _ X p d hX T _ N M l h₁ h₂ n hn Z i _ _ κ _ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have hproj : IsProjOver (strHom κ Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) =
        i ≫ p ≫ spMap (Int.castRingHom k) := specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by
      rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    exact ProperCurve.isProjOver_of_isProper _ hd
  let F₀ : HermLB.IsomClass p → ℤ :=
    Quotient.lift (s := HermLB.isometrySetoid p) (fun L => topSelfIntersection κ (L.B.pull i) 1) fun L L' e => by
      have ⟨w, hw, _⟩ := HermLB.Isometric.pull e i rfl
      exact interNum_congr_lbIso κ _ (fun _ => (L.restr i).isLB) (fun _ => (L'.restr i).isLB) fun _ => ⟨w, hw⟩
  let F : HermLB.IsomClass p →+ ℤ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨L'⟩
    exact HtTensCurve.topSelf_one_pull_tens hproj hd i L.isLB L'.isLB)
  have key (e : T × Fin N → ℤ) : topSelfIntersection κ ((ArInt.comb M e).B.pull i) 1 = ∑ x, e x * F (M x).icls := by
    change F (ArInt.comb M e).icls = _
    rw [icls_comb, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_zsmul, smul_eq_mul]
  rw [key]
  exact sum_neg_mul_nonneg T N _ (fun τ j hj => key _ ▸ h₁ τ j hj Z i κ hd) (fun τ => key _ ▸ (h₂ τ).1 Z i κ hd)
    (fun τ => key _ ▸ (h₂ τ).2 Z i κ hd) n hn

end GlobalTheory.HtNefAbel
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_combination_of_partial_indicators : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ}, IsArithVar p d → ∀ (T : Type) [Fintype T] (N : ℕ) (M : T × Fin N → HermLB p) (l : ℕ), (∀ τ : T, ∀ i : ℕ, i < N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l) → (∀ τ : T, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l) → ∀ n : T → Fin N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  atlas_forward_decl GlobalTheory.HtNefAbel.nefOver_comb_of_antitone
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

noncomputable section

namespace GlobalTheory.HtNefCore

theorem exists_cover_nefOver : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  intro h2 hH D O hc hf A T H hr c Q l hl hlp
  obtain ⟨V, M, hM, hA⟩ := GlobalTheory.T.adelic_norm_nef_partial_sums h2 hH D O hc hf A T H hr c Q l hl hlp
  refine ⟨V, M, hM, fun n hn => ?_⟩
  have hB := GlobalTheory.T.adelic_norm_nef_indicators h2 hH D O hc hf A T H hr c Q l hl hlp V M hM
  exact GlobalTheory.T.nef_combination_of_partial_indicators V.ar D.what₂.Tau O.N M l (fun τ i hi => by convert hA τ i hi) (fun τ => by convert hB τ using 3) n hn

end GlobalTheory.HtNefCore
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combined_metrized_bundle_nef_antitone : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  atlas_forward_decl GlobalTheory.HtNefCore.exists_cover_nefOver
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm GlobalTheory.CechPic

namespace GlobalTheory.VertForm

theorem nefOver_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k)
    (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (l : ℕ),
    l.Prime → NefOver L l → NefOver (L.pull π hπ) l := by
  intro k _ _ X Y p q hp hq π hπ L l hl hL Z i _ _ κ _ _ _ _ hd
  haveI : Fact l.Prime := ⟨hl⟩
  letI : Algebra (ZMod l) κ := ZMod.algebra κ l
  letI : Algebra (ZMod l) Γ(Z, ⊤) := ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ)).toAlgebra
  haveI : IsScalarTower (ZMod l) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨N, j, _, hj⟩ := hp
  obtain ⟨N', j', _, hj'⟩ := hq
  have := isProper_str k N
  have := isProper_str k N'
  have : IsProper q := hj' ▸ inferInstance
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have hp' : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := .of_comp π p
  have hg : IsProper ((i ≫ π) ≫ p ≫ spMap (Int.castRingHom k)) := inferInstance
  have h := GlobalTheory.ArInt.topSelf_pull_nonneg l (p ≫ spMap (Int.castRingHom k)) hd L.isLB (i ≫ π)
    fun Z' i' _ _ _ hd' => hL Z' i' (ZMod l) hd'
  have e : cls ((L.pull π hπ).B.pull i) (pull_isLB (L.pull π hπ).isLB i) =
      cls (L.B.pull (i ≫ π)) (pull_isLB L.isLB _) := by
    refine (cls_pull (L.pull π hπ).isLB i _).trans ?_
    refine Eq.trans ?_ (cls_pull L.isLB (i ≫ π) _).symm
    exact (pull_comp i π (cls L.B L.isLB)).symm
  rw [← topSelf_congr (ZMod l) (pull_isLB (L.pull π hπ).isLB i) (pull_isLB L.isLB _)
    ((cls_eq_iff _ _).1 e)] at h
  have e2 := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod l) κ Z (structureModule Z) (fun _ : Fin 1 => (L.pull π hπ).B.pull i)
  rw [topSelf_def] at h ⊢
  rw [e2] at h
  haveI : Module.Finite (ZMod l) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod l) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h

end GlobalTheory.VertForm
end
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_hermitian_bundle_pullback : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (l : ℕ), l.Prime → NefOver L l → NefOver (L.pull π hπ) l := by
  atlas_forward_decl GlobalTheory.VertForm.nefOver_pull
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.VertForm

namespace GlobalTheory.NefDescent

theorem nefOver_of_primeField {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (l : ℕ)
    [Fact l.Prime]
    (h : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod l) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod l) (L.B.pull i) 1) :
    NefOver L l := by
  intro Z i _ _ κ _ _ _ _ hdim
  letI : Algebra (ZMod l) κ := ZMod.algebra κ l
  letI : Algebra (ZMod l) Γ(Z, ⊤) := ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod l) κ)).toAlgebra
  haveI : IsScalarTower (ZMod l) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i hdim
  have e := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod l) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod l) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod l) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

theorem nefOver_of_pull : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), Function.Surjective π → ∀ (L : HermLB p) (l : ℕ), l.Prime → NefOver (L.pull π hπ) l → NefOver L l := by
  intro k _ _ X Y p q hp hq π hπ hsurj L l hl hL
  haveI : Fact l.Prime := ⟨hl⟩
  refine nefOver_of_primeField L l ?_
  intro Z i _ _ _ hd
  have : IsNoetherianRing k := IsNoetherianRing.of_finite ℤ k
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hp).1
  have : IsProper q := (isProper_and_exists_isAmpleLB_of_isProjOver hq).1
  have : IsProper (π ≫ p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π p
  have : Surjective π := ⟨hsurj⟩
  have : IsNoetherian Y := isNoetherian_of_isProjOver hq
  have : IsNoetherian X := isNoetherian_of_isProjOver hp
  have : IsNoetherian Z := by
    have := LocallyOfFiniteType.isLocallyNoetherian i
    have := QuasiCompact.compactSpace_of_compactSpace i
    exact {}
  let g := pullback.snd π i
  have : IsProper g := inferInstance
  have : Surjective g := inferInstance
  obtain ⟨w, hw, hdeg⟩ := fibre_point _ Z g (genericPoint Z) (g.surjective _)
  let C : Closeds (pullback π i : Scheme.{0}) := ⟨closure {w}, isClosed_closure⟩
  have : IsIntegral (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  have hgen := red_genericPoint _ w C rfl
  let f := redι C ≫ g
  let i' := redι C ≫ pullback.fst π i
  have hη : f (genericPoint _) = genericPoint Z := by
    simp only [f, Scheme.Hom.comp_apply, hgen, hw]
  have hdeg' : 0 < f.residueDegree (genericPoint _) := by
    simp only [f, CurveDegreesCompare.residueDegree_comp, hgen, GlobalTheory.Published.residueDegree_of_isClosedImmersion, mul_one]
    exact hdeg
  have hd' := dim_eq_one _ Z f hd hη hdeg'
  have : IsNoetherian (Scheme.IdealSheafData.vanishingIdeal C).subscheme := by
    have := LocallyOfFiniteType.isLocallyNoetherian i'
    have := QuasiCompact.compactSpace_of_compactSpace i'
    exact {}
  have : IsFinite f := isFinite_of_dim _ Z f hd' hd hη
  letI : Algebra (ZMod l) Γ((Scheme.IdealSheafData.vanishingIdeal C).subscheme, ⊤) := algebraΓAlong (ZMod l) f
  have h1 := hL _ i' (ZMod l) hd'
  have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
  have hcomm : i' ≫ π = f ≫ i := by simp only [i', f, g, Category.assoc, pullback.condition]
  have e1 : topSelfIntersection (ZMod l) ((L.pull π hπ).B.pull i') 1 = topSelfIntersection (ZMod l) ((L.B.pull i).pull f) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod l) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB π) i')
      (fun _ => LB.isLB_pull hN f) fun _ => ?_
    show pull i' (pull π (cls L.B L.isLB)) = pull f (pull i (cls L.B L.isLB))
    rw [← pull_comp, ← pull_comp, hcomm]
  have e2 : topSelfIntersection (ZMod l) ((L.B.pull i).pull f) 1 = interNumOn (ZMod l) f (fun _ : Fin 1 => L.B.pull i) :=
    (interNumOn_const_eq_topSelf (k := ZMod l) (fun _ => rfl) hN 1).symm
  have e3 : interNumOn (ZMod l) f (fun _ : Fin 1 => L.B.pull i) = interNumOn (ZMod l) f ![L.B.pull i] :=
    congrArg _ (funext fun j => by fin_cases j; rfl)
  have hproj : IsProjOver (strHom (ZMod l) Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l)) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom (ZMod l) Z ≫ spMap (Int.castRingHom (ZMod l))) := by rw [e]; infer_instance
    have : IsProper (strHom (ZMod l) Z) := IsProper.of_comp _ (spMap (Int.castRingHom (ZMod l)))
    exact ProperCurve.isProjOver_of_isProper _ hd
  have e4 := GlobalTheory.T.intersection_number_finite_pushforward (ZMod l) Z _ f hproj hd hη (L.B.pull i) hN
  have e5 : interNum (ZMod l) (structureModule Z) ![L.B.pull i] = topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
    rw [topSelf_def]
    exact congrArg _ (funext fun j => by fin_cases j; rfl)
  have hT : 0 ≤ (f.residueDegree (genericPoint _) : ℤ) * topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
    rw [← e5, ← e4, ← e3, ← e2, ← e1]
    exact h1
  exact nonneg_of_mul_nonneg_right hT (by exact_mod_cast hdeg')

end GlobalTheory.NefDescent

end
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VertForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_of_surjective_pullback_nef : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), Function.Surjective π → ∀ (L : HermLB p) (l : ℕ), l.Prime → NefOver (L.pull π hπ) l → NefOver L l := by
  atlas_forward_decl GlobalTheory.NefDescent.nefOver_of_pull
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtNef

open ReciprocityTheory.ChartRestriction.G GlobalTheory.CechPic in

theorem nefOver_iff_of_isometric {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {L L' : HermLB p}
    (h : L.Isometric L') (l : ℕ) : NefOver L l ↔ NefOver L' l := by
  obtain ⟨w, hw, -⟩ := h
  have e : cls L.B L.isLB = cls L'.B L'.isLB := (cls_eq_iff _ _).2 ⟨w, hw⟩
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)],
      topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (L'.B.pull i) 1 := fun Z i κ _ _ =>
    interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull L'.isLB i) fun _ => by
      rw [cls_pull L.isLB, cls_pull L'.isLB, e]
  constructor <;> intro H Z i _ _ κ _ _ _ _ hd
  · rw [← key]; exact H Z i κ hd
  · rw [key]; exact H Z i κ hd

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem map_genericPoint {V' V : Cover Y} (g : V'.G ⟶ V.G) (h : g ≫ V.π = V'.π) :
    g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

theorem surjective_of_lies {V' V : Cover Y} (π : V'.X ⟶ V.X) (hπ : π ≫ V.p = V'.p) (h : Lies V' V π) :
    Function.Surjective π := by
  obtain ⟨g, h₁, h₂⟩ := h
  have hη := (GlobalTheory.CoverDeg.map_genericPoint_and_deg F Y V V' π hπ g h₁.symm h₂ (map_genericPoint g h₂)).1
  have : IsProper V.p := (isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1
  have : IsProper V'.p := (isProper_and_exists_isAmpleLB_of_isProjOver V'.ar.isProjOver).1
  have : IsProper (π ≫ V.p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π V.p
  have hc : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  have hm : genericPoint V.X ∈ Set.range π := ⟨_, hη⟩
  have : closure {genericPoint V.X} ⊆ Set.range π := hc.closure_subset_iff.2 (Set.singleton_subset_iff.2 hm)
  rw [(genericPoint_spec V.X).def] at this
  exact fun z => this (Set.mem_univ z)

end GlobalTheory.HtNef

open GlobalTheory.HtNef in

theorem GlobalTheory.HtNef.nefOver_comb_root : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (V : Cover (O.var c)) (L : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (L x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → ∀ l ∈ Q, l.Prime → NefOver (ArInt.comb L fun x => -n x.1 x.2) l := by
  intro hP hH D O hC hf A T H h c Q V L hL n hn l hlQ hl
  obtain ⟨V₀, M, hM, hMn⟩ := GlobalTheory.T.combined_metrized_bundle_nef_antitone hP hH D O hC hf A T H h c Q l hlQ hl
  obtain ⟨V', π, π₀, hπ, hπ₀, l₁, l₀⟩ := GlobalTheory.T.common_refinement_covers _ _ V V₀
  have hs := surjective_of_lies π hπ l₁
  obtain ⟨g₁, e₁, f₁⟩ := l₁
  obtain ⟨g₀, e₀, f₀⟩ := l₀
  have hL' x := GlobalTheory.T.norms_pullback_along_cover _ _ V V' π hπ g₁ e₁.symm f₁ (map_genericPoint g₁ f₁) (L x) _ _ _ (hL x)
  have hM' x := GlobalTheory.T.norms_pullback_along_cover _ _ V₀ V' π₀ hπ₀ g₀ e₀.symm f₀ (map_genericPoint g₀ f₀) (M x) _ _ _ (hM x)
  have iso x := GlobalTheory.T.isometric_of_same_norms _ _ V' _ _ _ _ _ (hL' x) (hM' x)
  have n₀ : NefOver ((ArInt.comb M fun x => -n x.1 x.2).pull π₀ hπ₀) l :=
    GlobalTheory.T.nef_hermitian_bundle_pullback _ _ _ _ _ V₀.ar.isProjOver V'.ar.isProjOver π₀ hπ₀ _ l hl (hMn n hn)
  have i₁ := (isometric_comb_pull M (fun x => -n x.1 x.2) π₀ hπ₀).symm
  have i₂ := (isometric_comb_congr iso (fun x => -n x.1 x.2)).symm
  have i₃ := isometric_comb_pull L (fun x => -n x.1 x.2) π hπ
  have n₁ := (nefOver_iff_of_isometric (i₁.trans (i₂.trans i₃)) l).1 n₀
  exact GlobalTheory.T.nef_of_surjective_pullback_nef _ _ _ _ _ V.ar.isProjOver V'.ar.isProjOver π hπ hs _ l hl n₁

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_over_antitone_comb : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (V : Cover (O.var c)) (L : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (L x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → ∀ l ∈ Q, l.Prime → NefOver (ArInt.comb L fun x => -n x.1 x.2) l := by
  atlas_forward_decl GlobalTheory.HtNef.nefOver_comb_root
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm

namespace GlobalTheory.NefHodgeTateAt

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_of_cls_eq_add (hp : IsProjOver p) {N A B : LB X} (hN : N.IsLB) (hA : A.IsLB) (hB : B.IsLB)
    (h : cls N hN = cls A hA + cls B hB) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ (N.pull i) 1 = topSelfIntersection κ (A.pull i) 1 + topSelfIntersection κ (B.pull i) 1 := by
  obtain ⟨hpr, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have : IsFinite (spMap (Int.castRingHom k)) := by
    rw [spMap, IsFinite.SpecMap_iff]
    exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
  have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
    specZIsTerminal.hom_ext _ _
  have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
  have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
  have e2 (L : LB X) : topSelfIntersection κ (L.pull i) 1 = interNum κ (structureModule Z) ![L.pull i] := by
    rw [topSelf_def]
    congr 1
    funext j
    fin_cases j
    rfl
  rw [e2, e2, e2]
  refine interNum_one_of_cls_eq_add (hH.pull_of_isClosedImmersion i) hd (LB.isLB_pull hN i) (LB.isLB_pull hA i)
    (LB.isLB_pull hB i) ?_
  rw [cls_pull hN, cls_pull hA, cls_pull hB, h, map_add]

theorem topSelf_pow (hp : IsProjOver p) (L : HermLB p) (m : ℕ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
  have c (n : ℕ) : cls (L.pow n).B (L.pow n).isLB = n • cls L.B L.isLB := cls_lbPow L.isLB n _
  induction m with
  | zero =>
    have := topSelf_of_cls_eq_add hp (L.pow 0).isLB (L.pow 0).isLB (L.pow 0).isLB (by rw [c]; simp) Z i κ hd
    simp only [Nat.cast_zero, zero_mul]
    linarith
  | succ n ih =>
    rw [topSelf_of_cls_eq_add hp (L.pow (n + 1)).isLB (L.pow n).isLB L.isLB (by rw [c, c, succ_nsmul]) Z i κ hd, ih]
    push_cast
    ring

theorem nefOver_tens (hp : IsProjOver p) {L M : HermLB p} {l : ℕ} (hL : NefOver L l) (hM : NefOver M l) :
    NefOver (L.tens M) l := fun Z i _ _ κ _ _ _ _ hd => by
  rw [topSelf_of_cls_eq_add hp (L.tens M).isLB L.isLB M.isLB (cls_tens L.isLB M.isLB _) Z i κ hd]
  exact add_nonneg (hL Z i κ hd) (hM Z i κ hd)

theorem nefOver_pow (hp : IsProjOver p) {L : HermLB p} {l : ℕ} (hL : NefOver L l) (m : ℕ) :
    NefOver (L.pow m) l := fun Z i _ _ κ _ _ _ _ hd => by
  rw [topSelf_pow hp L m Z i κ hd]
  exact mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)

theorem nefOver_of_pow (hp : IsProjOver p) {L : HermLB p} {l m : ℕ} (hm : 0 < m) (hL : NefOver (L.pow m) l) :
    NefOver L l := fun Z i _ _ κ _ _ _ _ hd => by
  have h := hL Z i κ hd
  rw [topSelf_pow hp L m Z i κ hd] at h
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm)).1 h

omit [Module.Finite ℤ k] in

theorem nefOver_of_cls_eq {L M : HermLB p} {l : ℕ} (h : cls L.B L.isLB = cls M.B M.isLB) (hM : NefOver M l) :
    NefOver L l := fun Z i _ _ κ _ _ _ _ hd => by
  have : topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (M.B.pull i) 1 :=
    interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull M.isLB i) fun _ => by
      rw [cls_pull L.isLB, cls_pull M.isLB, h]
  rw [this]
  exact hM Z i κ hd

end Curves

theorem cls_eq_of_presents {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L M : LB X} {r : L.ι → X.functionFieldˣ}
    {r' : M.ι → X.functionFieldˣ} (h : Presents D L r) (h' : Presents D M r') : cls L h.isLB = cls M h'.isLB := by
  choose a ha using fun q : M.ι × L.ι => exists_unit_fnOf_eq (U := M.U q.1 ⊓ L.U q.2)
    fun x hx => (h.isEqn _ x hx.2).iff_unitAt.1 (h'.isEqn _ x hx.1)
  refine (cls_eq_iff _ _).2 ⟨⟨a⟩, fun p q => Units.ext (Cartier.fn_ext fun hpq => ?_)⟩
  have e := congrArg (fnOf (L.U p.2 ⊓ L.U q.2) (memInf hpq.1.2 hpq.2.2)) (L.g p.2 q.2).inv_mul
  rw [map_mul, map_one] at e
  refine (fnOf_resG _ hpq _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ hpq _) (fnOf_resG _ hpq _)))
    (fnOf_resG _ hpq _))).symm)
  refine (ha p _).trans (Eq.trans ?_ (congrArg _ (ha q _)).symm)
  rw [h.isRatSec p.2 q.2 (memInf hpq.1.2 hpq.2.2), h'.isRatSec p.1 q.1 (memInf hpq.1.1 hpq.2.1),
    mul_div_mul_comm, div_eq_mul_inv, ← eq_inv_of_mul_eq_one_left e]
  rfl

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem j_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h₁ (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
    change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
    have := ((V.π ≫ Y.str) y).isPrime
    rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have h₂ {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
    rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
    change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans (h₁ _).le)
  obtain ⟨y, hy⟩ := h₂ h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem w_div_eq_one {Z : Scheme.{0}} [IsIntegral Z] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (z : Sp (AlgebraicClosure F) ⟶ Z) {c a b : Z.functionField} (ha : UnitAt (below z) (c * a))
    (hb : UnitAt (below z) (c * b))
    (h : Real.log (e.w (valAt z (c * a))) = Real.log (e.w (valAt z (c * b)))) :
    e.w (valAt z (b / a)) = 1 := by
  have hc : c ≠ 0 := left_ne_zero_of_mul ha.ne_zero
  have ha0 : a ≠ 0 := right_ne_zero_of_mul ha.ne_zero
  have e₁ : b / a = (c * b) * (c * a)⁻¹ := by field_simp
  have pa := e.w.pos (SmallSec.valAt_ne_zero ha)
  have pb := e.w.pos (SmallSec.valAt_ne_zero hb)
  have e₂ := Real.log_injOn_pos pa pb h
  rw [e₁, SmallSec.valAt_mul hb.regAt ha.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv ha, map_mul, map_inv₀, ← e₂,
    mul_inv_cancel₀ pa.ne']

theorem cls_eq_of_norms {V : Cover Y} {L L' : HermLB V.p} {f : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (h' : Norms V L' f a' l) :
    cls L.B L.isLB = cls L'.B L'.isLB := by
  obtain ⟨r, hr, hu, -, hf⟩ := h
  obtain ⟨r', hr', hu', -, hf'⟩ := h'
  haveI := CoverHt.isPreimmersion_j V
  have hη := j_specializes V
  let ρ : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  have hρ : ∀ (U : V.X.Opens) (hU : genericPoint V.X ∈ U) (hU' : genericPoint V.G ∈ V.j ⁻¹ᵁ U) (s : Γ(V.X, U)),
      ρ (fnOf U hU s) = fnOf (V.j ⁻¹ᵁ U) hU' (V.j.app U s) := fun U hU hU' s => SmallSec.fnMap_fnOf V.j hη hU hU' s
  have hj : V.j (genericPoint V.G) = genericPoint V.X := (hη.antisymm (genericPoint_specializes _)).eq
  have hv : ∀ {K : Type} [Field K] (y : Sp K ⟶ V.G) (g : V.X.functionField), valAt (y ≫ V.j) g = valAt y (ρ g) :=
    fun y g => ModelFn.valAt_comp V.j hη y g
  have hR := InducedIsom.isRatSec_lift V.j ρ hρ hj L.B hr
  have hR' := InducedIsom.isRatSec_lift V.j ρ hρ hj L'.B hr'
  have hP := presents_divOfRatSec L.isLB hR
  have eρ (a b : V.G.functionFieldˣ) : ρ ((Units.map ρ.symm.toMonoidHom b : V.X.functionField) /
      (Units.map ρ.symm.toMonoidHom a : V.X.functionField)) = (b : V.G.functionField) / a := by
    rw [map_div₀]
    exact congrArg₂ (· / ·) (ρ.apply_symm_apply _) (ρ.apply_symm_apply _)
  have key : ∀ (i : L.B.ι) (j : L'.B.ι) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
      (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) →
      spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ (L.B.U i ⊓ L'.B.U j) →
      e.w (valAt z (((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField) /
        ((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField))) = 1 ∧
      e.w (valAt z (((r fun _ => i : V.G.functionFieldˣ) : V.G.functionField) /
        ((r' fun _ => j : V.G.functionFieldˣ) : V.G.functionField))) = 1 := by
    intro i j v e z yt hz e₂ hU
    let y : AlgPt Y := ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩
    have h₁ : ⊤ ≤ yt ⁻¹ᵁ L.B.U ((fun _ => i : (L.B.pull V.j).ι) PUnit.unit) := fun w hw => (hU hw).1
    have h₂ : ⊤ ≤ yt ⁻¹ᵁ L'.B.U ((fun _ => j : (L'.B.pull V.j).ι) PUnit.unit) := fun w hw => (hU hw).2
    have H₁ := hf v e y z yt (fun _ => i) rfl e₂ h₁
    have H₂ := hf' v e y z yt (fun _ => j) rfl e₂ h₂
    have hpt : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ L.B.U i ⊓ L'.B.U j := by
      rw [← e₂]
      exact hU (Set.mem_univ _)
    have m₁ : below z ∈ (L.B.pull V.j).U (fun _ => i) := Set.mem_iInter.2 fun _ => hpt.1
    have m₂ : below z ∈ (L'.B.pull V.j).U (fun _ => j) := Set.mem_iInter.2 fun _ => hpt.2
    have hπ : V.π (below z) = below y.1 := rfl
    have u₁ := hu _ _ m₁
    have u₂ := hu' _ _ m₂
    rw [hπ] at u₁ u₂
    exact ⟨w_div_eq_one e z u₁ u₂ (H₁.symm.trans H₂), w_div_eq_one e z u₂ u₁ (H₂.symm.trans H₁)⟩
  refine cls_eq_of_presents hP ⟨L'.isLB, hR', fun j x hxj => ?_⟩
  obtain ⟨i, hxi⟩ := exists_chart L.isLB x
  refine (hP.isEqn i x hxi).iff_unitAt.2
    ((unitAt_iff (div_ne_zero (Units.ne_zero _) (Units.ne_zero _))).2 ⟨?_, ?_⟩)
  · refine Cover.RegCrit.regAt_of_integral_values F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩
    rw [hv, eρ]
    exact (key i j v e z yt hz h hU).1.le
  · rw [inv_div]
    refine Cover.RegCrit.regAt_of_integral_values F Y V (L.B.U i ⊓ L'.B.U j) _ (fun v e z yt hz h hU => ?_) x ⟨hxi, hxj⟩
    rw [hv, eρ]
    exact (key i j v e z yt hz h hU).2.le

theorem norms_scale {V : Cover Y} {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) {b : F} (hb : b ≠ 0) :
    ∃ a', Norms V L f a' fun v e y => Real.log (NumberField.HeightOneSpectrum.adicAbv F v b) + l v e y := by
  have hu (x : Y.X) := IndScale.unitAt_constFn Y.str x hb
  obtain ⟨r, hr, h₁, h₂, h₃⟩ := norms_mul_unit F Y V L f a l (fun _ => Cartier.constFn Y.str b) hu h
  let c : V.G.functionFieldˣ := Units.mk0 (V.φ (Cartier.constFn Y.str b))
    ((map_ne_zero V.φ).2 (hu (genericPoint Y.X)).ne_zero)
  have e (g : Y.Fn) (i) : V.φ g * ((c * r i : V.G.functionFieldˣ) : V.G.functionField) =
      V.φ (Cartier.constFn Y.str b * g) * r i := by
    rw [map_mul, Units.val_mul, Units.val_mk0]
    ring
  refine ⟨fun σ y => Real.log ‖ratVal (Cartier.constFn Y.str b) y‖ + a σ y, fun i => c * r i, fun i j hij => ?_,
    fun i x hx => ?_, fun σ z y y' i e₁ e₂ hi => ?_, fun v ε y z yt i e₁ e₂ hi => ?_⟩
  · rw [Units.val_mul, Units.val_mul, hr i j hij]
    ring
  · rw [e]
    exact h₁ i x hx
  · rw [e]
    exact h₂ σ z y y' i e₁ e₂ hi
  · have := h₃ v ε y z yt i e₁ e₂ hi
    beta_reduce at this
    rw [IndScale.valAt_constFn Y.str _ y.1 y.2, ε.w_alg] at this
    rw [e]
    exact this

theorem exists_integral_point (V : Cover Y) (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) :
    ∃ (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 ∧
      spMap e.O.subtype ≫ yt = z ≫ V.j := by
  obtain ⟨y⟩ := ValGroup.nonempty_algPt Y
  obtain ⟨z, hz⟩ := exists_lift_pt V.π y.1
  have hP : IsProper V.p := (isProper_and_exists_isAmpleLB_of_isProjOver V.ar.isProjOver).1
  have hmem : ∀ a : 𝓞 F, ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)) a ∈ e.O := by
    intro a
    rw [e.mem_O, RingHom.comp_apply, e.w_alg]
    exact IsDedekindDomain.HeightOneSpectrum.adicAbv_coe_le_one (K := F) v
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) a
  let φ : 𝓞 F →+* e.O := ((algebraMap F (AlgebraicClosure F)).comp (algebraMap (𝓞 F) F)).codRestrict e.O.toSubring hmem
  have hE : ValuativeCriterion.Existence V.p := by
    have h : UniversallyClosed V.p := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have hsq : CommSq (z ≫ V.j) (Spec.map (CommRingCat.ofHom (algebraMap e.O (AlgebraicClosure F)))) V.p (spMap φ) := by
    refine ⟨?_⟩
    rw [Category.assoc, V.pb.w, ← Category.assoc, ← Category.assoc z, hz, y.2, ← Spec.map_comp, ← Spec.map_comp]
    rfl
  obtain ⟨⟨l⟩⟩ := hE { R := e.O, K := AlgebraicClosure F, i₁ := z ≫ V.j, i₂ := spMap φ, commSq := hsq }
  exact ⟨y, z, l.l, hz, l.fac_left⟩

theorem nefOver_of_norms {V : Cover Y} {L L' : HermLB V.p} {f : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} {c : HeightOneSpectrum (𝓞 F) → ℝ}
    (hc : (Function.support c).Finite) (h : Norms V L f a fun v e y => l v e y + c v) (h' : Norms V L' f a' l) {q : ℕ}
    (hq : NefOver L' q) : NefOver L q := by
  obtain ⟨m, b, b', hb, hb', E⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F c hc fun v => by
    obtain ⟨e⟩ : Nonempty (Ext v) := inferInstance
    obtain ⟨y, z, yt, e₁, e₂⟩ := exists_integral_point V v e
    obtain ⟨r, -, -, -, hf⟩ := h
    obtain ⟨r', -, -, -, hf'⟩ := h'
    have chart (B : HermLB V.p) : ∃ i, ⊤ ≤ yt ⁻¹ᵁ B.B.U i := by
      obtain ⟨i, hi⟩ := exists_chart B.isLB (yt (IsLocalRing.closedPoint e.O))
      exact ⟨i, ((IsLocalRing.closedPoint_mem_iff (R := e.O) (yt ⁻¹ᵁ B.B.U i)).1 hi).ge⟩
    obtain ⟨i, hi⟩ := chart L
    obtain ⟨i', hi'⟩ := chart L'
    have h₁ := hf v e y z yt (fun _ => i) e₁ e₂ hi
    have h₂ := hf' v e y z yt (fun _ => i') e₁ e₂ hi'
    obtain ⟨α, hα, h₃⟩ := ValGroup.exists_log_sub e.w
      (valAt z (V.φ (f (below y.1)) * (r' fun _ => i' : V.G.functionFieldˣ)))
      (valAt z (V.φ (f (below y.1)) * (r fun _ => i : V.G.functionFieldˣ)))
    have : c v = Real.log (e.w α) := by
      rw [← h₃, ← h₁, ← h₂]
      ring
    rw [this]
    exact GlobalTheory.ExtValueGroup.log_w_rat F v e α hα
  have ne {x : 𝓞 F} (hx : x ≠ 0) : algebraMap (𝓞 F) F x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hx
  obtain ⟨a₁, h₁⟩ := norms_scale (norms_pow F Y V L _ _ _ m h) (ne hb')
  obtain ⟨a₂, h₂⟩ := norms_scale (norms_pow F Y V L' _ _ _ m h') (ne hb)
  have hcl := cls_eq_of_norms h₁ (h₂.congr (fun _ => rfl) (fun _ _ => rfl) fun v e y => by
    linear_combination -E v)
  exact nefOver_of_pow V.ar.isProjOver m.pos (nefOver_of_cls_eq hcl (nefOver_pow V.ar.isProjOver hq m))

theorem norms_of_comb {V : Cover Y} {C : CxSt F} {A : Adl C Y} {ι : Type} [Fintype ι] {ρ : ι → Adl C Y} {q : ℕ} {b : ι → ℤ}
    (hD : q • A.D = ∑ i, b i • (ρ i).D)
    (hfin : ∀ v e y, q * A.lg v e y =
      Real.log (e.w (valAt y.1 (genAt A.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) +
        ∑ i, b i * (ρ i).lg v e y) {N : HermLB V.p} {K : ℕ} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    (h : Norms V N (fun x => (∏ i, genAt (ρ i).D x ^ b i) ^ K) a fun v e y => K * ∑ i, b i * (ρ i).lg v e y) :
    ∃ a', Norms V N (fun x => genAt A.D x ^ (K * q)) a' fun v e y => ((K * q : ℕ) : ℝ) * A.lg v e y := by
  classical
  have hu0 : ∀ x, UnitAt x (genAt A.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i) := by
    intro x
    have h₁ := (Base.isEqn_eqn A.D x).nsmul q
    have h₂ : (∑ i, b i • (ρ i).D).IsEqn x (∏ i, eqn (ρ i).D x ^ b i) := by
      have key : ∀ s : Finset ι, (∑ i ∈ s, b i • (ρ i).D).IsEqn x (∏ i ∈ s, eqn (ρ i).D x ^ b i) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using CartierDiv.isEqn_zero x
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.prod_insert hj]
          exact ((Base.isEqn_eqn (ρ j).D x).zsmul (b j)).add ih
      exact key _
    rw [hD] at h₁
    have h₃ := h₁.iff_unitAt.1 h₂
    convert h₃ using 1
    simp only [genAt, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Units.coe_prod, inv_pow, inv_zpow', Finset.prod_inv_distrib]
    simp only [zpow_neg, Finset.prod_inv_distrib, div_inv_eq_mul]
    rw [mul_comm, div_eq_mul_inv]
  have hP : ∀ x, (∏ i, genAt (ρ i).D x ^ b i) ≠ 0 := fun x =>
    Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (Units.ne_zero _)
  have h2 := norms_mul_unit F Y V _ _ _ _ (fun x => (genAt A.D x ^ q / ∏ i, genAt (ρ i).D x ^ b i) ^ K)
    (fun x => InducedPow.unitAt_pow (hu0 x) K) h
  refine ⟨_, h2.congr (fun x => ?_) (fun _ _ => rfl) fun v w y => ?_⟩
  · rw [← mul_pow, div_mul_cancel₀ _ (hP x), ← pow_mul, mul_comm q K]
  · rw [InducedPow.valAt_pow _ (hu0 _).regAt K, map_pow, Real.log_pow]
    have H := hfin v w y
    generalize Real.log (w.w (TrueGeo.valAt y.1 (genAt A.D (below y.1) ^ q / ∏ i, genAt (ρ i).D (below y.1) ^ b i))) = Aq at H ⊢
    push_cast
    linear_combination -(K : ℝ) * H

theorem nefAt_of_cover {C : CxSt F} {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+}
    {cf : HeightOneSpectrum (𝓞 F) → ℝ} (hI : A.Induced M L k cf) (V : Cover Y) (l : ℕ) [Fact l.Prime]
    (h : ∀ V' : Cover Y, (∀ (B : HermLB V.p) f a g, Norms V B f a g → ∃ B' : HermLB V'.p, Norms V' B' f a g) →
      ∃ (N : HermLB V'.p) (m : ℕ) (a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ), 0 < m ∧
        (Norms V' N (fun x => genAt A.D x ^ m) a fun v e y => m * A.lg v e y) ∧ NefOver N l)
    (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod l) Γ(Z, ⊤)]
    (hd : topologicalKrullDim Z = 1) : 0 ≤ topSelfIntersection (ZMod l) (L.B.pull i) 1 := by
  obtain ⟨P, π, -, hP, hπ, -, hj, -, hU, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M
  have h₁ := InducedPull.induced_pull F C Y A M P π hπ hj L k cf hI
  have h₂ := h₁.twist_fin (c := -cf) (by rw [Function.support_neg]; exact hI.1)
  rw [add_neg_cancel] at h₂
  have h₃ := norms_of_induces (Cover.induces_ofModel hP h₂)
  obtain ⟨V', a, g, b, ha, hb, e₁, e₂, e₃, e₄⟩ := CoverDom.exists_cover_dominating F Y V P
  have hη : V'.π (genericPoint V'.G) = genericPoint Y.X := by
    have := (genericPoint_spec V'.G).image V'.π.continuous
    rw [Set.image_univ, V'.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  have h₄ := GlobalTheory.T.norms_pullback_along_cover F Y (Cover.ofModel P hP) V' b hb V'.π e₄ (Category.comp_id _) hη _ _ _ _ h₃
  have hbη := (CoverDeg.map_genericPoint_and_deg F Y (Cover.ofModel P hP) V' b hb V'.π e₄ (Category.comp_id _) hη).1
  obtain ⟨N, m, aN, hm, hN, hnef⟩ := h V' fun B f a' g' hB =>
    ⟨_, GlobalTheory.T.norms_pullback_along_cover F Y V V' a ha g e₁ e₂ e₃ B f a' g' hB⟩
  have h₅ := norms_pow F Y V' _ _ _ _ m h₄
  have h₆ := norms_pow F Y V' _ _ _ _ k hN
  have h₇ : NefOver (((L.pull π hπ).pull b hb).pow m) l :=
    nefOver_of_norms (c := fun v => (m : ℝ) * k * (A.n : ℕ) * cf v)
      (hI.1.subset fun v hv h0 => hv (by simp [h0]))
      (h₅.congr (fun x => by rw [← pow_mul, ← pow_mul, mul_comm]; rfl) (fun _ _ => rfl) fun v e y => by
        simp only [Adl.twist, Pi.neg_apply]
        ring) h₆ (nefOver_pow V'.ar.isProjOver hnef k)
  have h₈ := nefOver_of_pow V'.ar.isProjOver hm h₇
  have := P.ar.isIntegral
  have : IsProper P.p := (isProper_and_exists_isAmpleLB_of_isProjOver P.ar.isProjOver).1
  have : IsProper (b ≫ P.p) := by
    rw [hb]
    exact (isProper_and_exists_isAmpleLB_of_isProjOver V'.ar.isProjOver).1
  have : IsProper b := IsProper.of_comp b P.p
  have hbs : Function.Surjective b := fun x =>
    (genericPoint_specializes x).mem_closed b.isClosedMap.isClosed_range ⟨_, hbη⟩
  exact NefDeRhamAt.nefAt_of_pull _ M.X P.X M.p P.p M.ar.isProjOver P.ar.isProjOver π hπ
    (NefFibUniq.surjective_of_models M P π hπ hU) L l
    (NefDeRhamAt.nefAt_of_pull _ P.X V'.X P.p V'.p P.ar.isProjOver V'.ar.isProjOver b hb hbs _ l
      fun Z i _ _ _ hd => h₈ Z i (ZMod l) hd) Z i hd

end Covers

open Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4
open scoped ENNReal Classical

theorem nefAt_of_weights (hP : Hypotheses2) {D : D7} {O : Setup D} (hO : O.Core) {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y}
    (h : O.Reads A T H) {B : ℝ} (hB : 2 ≤ B) {u : Wt O.Y} {s : ℚ} (hu : IsRat O.Y u) (hs : 0 < s)
    (hdom : WeightThresholdDefs.Dominant O.Y (A.sh u s)) (c : O.s.Comp) (q : ℕ) [Fact q.Prime]
    (hw : ∀ (V : Cover (O.var c)) (L : DV.Rt D.what₂.Tau O.N → HermLB V.p),
      (∀ x, Norms V (L x) (fun z => genAt (O.root0 c (FlagAr.setB O.Y B) x).D z)
        (fun σ y => lnAdl (O.root0 c (FlagAr.setB O.Y B) x) σ y) fun v e y => (O.root0 c (FlagAr.setB O.Y B) x).lg v e y) →
      ∀ n : D.what₂.Tau → Fin O.N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb L fun x => -n x.1 x.2) q)
    {M : TrueGeo.Model (O.var c)} {L : HermLB M.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ}
    (hI : (O.Mb B u s c).Induced M L k cf) (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z]
    [Algebra (ZMod q) Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) : 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1 := by
  have hab : (O.met.ab c).NefFib := by
    obtain ⟨x, P, hc⟩ := hO
    rw [hc.ab_eq]
    exact P.nefFib_ab c
  obtain ⟨m, b, hm, hb, hD, -, hfin⟩ := hO.mbIs B hB u s hu hs (A.sh u s)
    (by rw [← h.aux.dir]; rfl) hdom c
  let W := h.mdl (FlagAr.setB O.Y B) c
  refine nefAt_of_cover hI W.V q (fun V pl => ?_) Z i hd
  obtain ⟨amp, hamp⟩ := pl _ _ _ _ (norms_of_induces W.amp_spec)
  choose R hR using fun x => pl _ _ _ _ (norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c W _ subset_rfl x))
  replace hR := fun x => (hR x).congr (f' := fun z => genAt (O.root0 c (FlagAr.setB O.Y B) x).D z)
    (a' := fun σ y => lnAdl (O.root0 c (FlagAr.setB O.Y B) x) σ y)
    (l' := fun v e y => (O.root0 c (FlagAr.setB O.Y B) x).lg v e y) (fun _ => pow_one _) (fun _ _ => by simp)
    fun _ _ _ => by simp
  have hmn : (0 : ℝ) < (m : ℝ) * ((O.Mb B u s c).n : ℕ) := mul_pos (Nat.cast_pos.2 hm) (Nat.cast_pos.2 (O.Mb B u s c).n.2)
  have hb0 : 0 ≤ b none := by
    have h₁ : (m : ℝ) * ((O.Mb B u s c).n : ℕ) * (s : ℝ) = b none * ((O.met.ab c).n : ℕ) := hb none
    have h₂ : (0 : ℝ) < b none * ((O.met.ab c).n : ℕ) := h₁ ▸ mul_pos hmn (by exact_mod_cast hs)
    have h₃ : (0 : ℝ) < b none := by
      by_contra hh
      push Not at hh
      nlinarith [(Nat.cast_nonneg ((O.met.ab c).n : ℕ) : (0 : ℝ) ≤ _)]
    exact_mod_cast h₃.le
  have hbx (x : DV.Rt D.what₂.Tau O.N) : (m : ℝ) * ((O.Mb B u s c).n : ℕ) * -A.sh u s x.1 x.2 = b (some x) :=
    (hb (some x)).trans (by
      change _ * (((1 : ℕ+) : ℕ) : ℝ) = _
      simp)
  have hn := hw V R hR (fun τ j => -b (some (τ, j))) fun τ j j' hj => by
    have h₁ := hbx (τ, j)
    have h₂ := hbx (τ, j')
    have h₃ := mul_le_mul_of_nonneg_left (hdom τ j j' hj) hmn.le
    have : ((-b (some (τ, j')) : ℤ) : ℝ) ≤ (-b (some (τ, j)) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  simp only [neg_neg] at hn
  have hna := (nefFib_iff amp).1 (GlobalTheory.T.nef_fibre_of_norms_power hP _ _ _ hab V amp W.k W.k_pos hamp) q Fact.out
  have hN := norms_tens _ _ V _ _ _ _ _ _ _ _ (norms_pow _ _ V _ _ _ _ (b none).toNat hamp)
    (norms_pow _ _ V _ _ _ _ W.k (norms_comb hR fun x => b (some x)))
  have hc : (((b none).toNat : ℕ) : ℝ) = b none := by exact_mod_cast Int.toNat_of_nonneg hb0
  obtain ⟨a', ha'⟩ := norms_of_comb (K := W.k) hD hfin (hN.congr (fun x => by
    rw [Fintype.prod_option, mul_pow, ← pow_mul, mul_comm W.k, pow_mul]
    refine congrArg₂ (· * ·) (congrArg (· ^ W.k) ?_) rfl
    rw [← zpow_natCast, Int.toNat_of_nonneg hb0]
    rfl) (fun _ _ => rfl) fun v e y => by
    rw [Fintype.sum_option, hc]
    simp only [Option.elim]
    ring)
  exact ⟨_, W.k * m, a', Nat.mul_pos W.k_pos hm, ha',
    nefOver_tens V.ar.isProjOver (nefOver_pow V.ar.isProjOver hna _) (nefOver_pow V.ar.isProjOver hn _)⟩

theorem nefAt_HT : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), O.Reads A T H →
  ∀ (B : ℝ), 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → WeightThresholdDefs.Dominant O.Y (A.sh u s) →
  ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
  (O.Mb B u s c).Induced M L k cf → ∀ (Z : Scheme.{0}) (i : Z ⟶ M.X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ)
  [Fact q.Prime] [Algebra (ZMod q) Γ(Z, ⊤)], q ∈ FlagAr.setB O.Y B → topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1 := by
  intro hP hH D O hO hf A T H hR B hB u s hu hs hdom c M L k cf hI Z i _ _ q _ _ hq hd
  exact nefAt_of_weights hP hO hR hB hu hs hdom c q
    (fun V R hR' n hn => GlobalTheory.T.nef_over_antitone_comb hP hH D O hO hf A T H hR c _ V R hR' n hn q hq Fact.out) hI Z i hd

end GlobalTheory.NefHodgeTateAt
end
end
