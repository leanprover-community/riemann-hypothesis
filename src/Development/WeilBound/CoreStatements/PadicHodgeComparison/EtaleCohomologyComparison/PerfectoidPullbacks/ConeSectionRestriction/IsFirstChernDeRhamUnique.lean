import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonempty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedQuotientVanishAboveDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupPowerSmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowKPull
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartPropertyPropagates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartUnionLeSite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartRestrictPullBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningFiltrationIsFilStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentativeRestrict
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCupListRepresentativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitLogRepresentativeCompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCochainExtendOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopRepresentativeAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusJacobianDet
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCoverVanishingInduction
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningGradedVanishNegative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioIsUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalRestrictSection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobianSpanLeSubalgebra
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectiveChartAffineCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLiftStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocVan
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeometricGenericComponents
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidStmt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdealStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTwistingLineDataProjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistingSheafBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem oneK_ne_zero : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := GlobalTheory.T.unit_class_ne_zero_of_nonempty

theorem gr_top_van : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V → ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r →
    Subsingleton (HQ (KS q s {V}) r (r + 1) j) := GlobalTheory.T.affine_graded_quotient_vanish_above_dim

theorem cupPowC_smul : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    (z : CH.Cn (CH.modF A) 2) (a : R) (k : ℕ), cupPowC A (a • z) k = a ^ k • cupPowC A z k := GlobalTheory.T.cup_power_smul

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

theorem wch_mem : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D := GlobalTheory.T.chart_open_mem_cover_of_O1

theorem wK_rel : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (k : Fin m) ⦃T T' : Thick (smFun X q)⦄,
    (T ⟶ T') → wK q i y s k T → (∃ β, wK q i y s β T') → wK q i y s k T' := GlobalTheory.T.chart_property_propagates

theorem wU_le : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ), IsTautologicalLineAt D N i → wU q i y s ≤ KS q s (𝒱D D) := GlobalTheory.T.chart_union_le_site

theorem zar_capS : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {N m : ℕ}
    (i : X ⟶ PSpace K N) (y : Fin m → MvPolynomial (Fin (N + 1)) K) (s : ℕ) (S : Finset (Fin m)) (hS : S.Nonempty)
    (r r' : ℤ) (j : ℕ),
    ∃ h : capS (wK q i y s) S ≤ KS q s {⨅ k ∈ S, uy i y k},
      Function.Bijective ((resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) h).pull j) := GlobalTheory.T.chart_restrict_pull_bijective

theorem isFil_th : ∀ {b : Base} (L : b.Fun), IsFil (thP L) (thFil L) := GlobalTheory.T.thickening_filtration_isFil

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem rep_cupList : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {m : ℕ} (ℓ : Fin m → CH.Cn (CH.modF Φ.A) 1), (∀ k, CH.d _ 1 (ℓ k) = 0) → (∀ k σ, ℓ k σ ∈ (Fil 1).S _) →
    ∃ c : CH.H (sq (Fil m) (Fil ((m : ℤ) + 1))) m, Rep (Fil m) (Fil ((m : ℤ) + 1)) (cupListC Φ.A ℓ) c := GlobalTheory.T.exists_cup_list_representative

theorem dlog_ratios : ∀ {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := GlobalTheory.T.torus_jacobian_det

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb

theorem cech_top_rel : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ (s n : ℕ) (W : Fin (n + 2) → ObjectProperty C), (∀ T, (∃ α, W α T) → (Fil s).S T = ⊥) →
    (∀ α ⦃T T' : C⦄, (T ⟶ T') → W α T → (∃ β, W β T') → W α T') →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r → Subsingleton (HU (gr Fil r) (capS W S) j)) →
    ∀ (z : CH.Cn (CH.modF ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A)) 2), CH.d _ 2 z = 0 → (∀ σ, z σ ∈ (Fil 1).S _) →
    ∀ (b : ∀ i, CH.Cn (CH.modF ((W i).ι ⋙ Φ.A)) 1), (∀ i σ, b i σ ∈ (Fil 1).S _) →
    (∀ i, resB Φ.A (fun T h => ⟨i, h⟩ : W i ≤ fun T : C => ∃ α, W α T) z = CH.d _ 1 (b i)) →
    (∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T : C => ∃ α, W α T) ⋙ Φ.A) z (n + 1)) h = 0) →
    ∀ c : HU (gr Fil ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
      Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
        (cupListC ((capS W Finset.univ).ι ⋙ Φ.A) fun k : Fin (n + 1) =>
          resB Φ.A (capS_le_univ W k.castSucc) (b k.castSucc) - resB Φ.A (capS_le_univ W k.succ) (b k.succ)) c →
      ∃ (ω : ∀ i, HU (gr Fil ((n : ℤ) + 1)) (capS W (Finset.univ.erase i)) (n + 1))
        (f : CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ Φ.A)) n),
        (∀ σ, f σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
        Rep ((Fil ((n : ℤ) + 1)).res (capS W Finset.univ).ι) ((Fil ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (CH.d _ n f) (c - ∑ i, ((resU (gr Fil ((n : ℤ) + 1)) (capS_univ_le W (Finset.univ.erase i))).pull (n + 1)) (ω i)) := GlobalTheory.T.graded_cover_vanishing_induction

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb.LocalCohomologySetup

attribute [local instance] MvPolynomial.gradedAlgebra

open CrystallineSemistableComparison.Pb

def ResidAlgP : Prop := ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [Algebra K R]
    (t : Fin (n + 1) → Rˣ), AlgebraicIndependent K (fun k => (t k : R)) →
    ∀ (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    ∀ (B : Finset (Fin (n + 2)) → Subalgebra K R), (∀ S, S.Nonempty → torusS K t S ≤ B S) → (∀ S, S.Nonempty → (B S).FG) →
    (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K t S) b) → (∀ i, B (Finset.univ.erase i) ≤ B Finset.univ) →
    (∀ r : R, ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b) →
    ∀ (ω : Fin (n + 2) → R) (η : Fin (n + 1) → R), (∀ i, ω i ∈ jacS (B (Finset.univ.erase i)) D id) →
      (∀ k, η k ∈ jacS (B Finset.univ) D (Fin.succAbove k)) →
      ((∏ k, t k)⁻¹ : Rˣ) ≠ (∑ i, ω i + ∑ k : Fin (n + 1), (-1 : R) ^ (k : ℕ) * D k (η k) : R)

def LocExactP : Prop := ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} [CharZero K] (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (i : X ⟶ PSpace K N)
    (hD : IsTautologicalLineAt D N i) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e)
    (s : ℕ) (Λ : CLiftK (ObjectProperty.ι fun T : Thick (smFun X q) => ∃ k, wK q i y s k T) D),
    ∃ b : ∀ k, CH.Cn (CH.modF ((wK q i y s k).ι ⋙ thA (smFun X q))) 1,
      (∀ k σ, b k σ ∈ (thFil (smFun X q) 1).S _) ∧
      (∀ k, resB (thA (smFun X q)) (fun T h => ⟨k, h⟩ : wK q i y s k ≤ fun T : Thick (smFun X q) => ∃ k', wK q i y s k' T)
        (e • zK Λ s) = CH.d _ 1 (b k)) ∧
      ∀ k k', ∃ ĝ : ∀ T : (capS (wK q i y s) {k, k'}).FullSubcategory, T.obj.B,
        (∀ T (h : InU (uy i y k') T.obj),
          Ideal.Quotient.mk _ (ĝ T) = ev T.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k'))) ∧
        resB (thA (smFun X q)) (fun T h => h k (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k) (b k) -
          resB (thA (smFun X q)) (fun T h => h k' (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k') (b k') =
          dlogC (capS (wK q i y s) {k, k'}) s ĝ

def GeoSetupP : Prop := ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension (n + 1) q] (N : ℕ) (i : X ⟶ PSpace K N)
    (_ : IsClosedImmersion i) (_ : i ≫ PSpace.str K N = q),
    ∃ (e : ℕ) (_ : 0 < e) (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e),
      let U : Fin (n + 2) → X.Opens := fun k => i ⁻¹ᵁ Proj.basicOpen _ (y k)
      (⨆ k, U k) = ⊤ ∧
      (∀ S : Finset (Fin (n + 2)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, U k)) ∧
      ∃ (V : X.Opens) (hV : V ≤ ⨅ k, U k) (c : Coord q V (n + 1)),
        letI := (strV q V).toAlgebra
        IsDomain Γ(X, V) ∧
        (∀ k, c.t k = (i.appLE _ V (hV.trans (iInf_le U 0))).hom (yRatio y hy k)) ∧
        ∃ ht : ∀ k, IsUnit (c.t k),
          AlgebraicIndependent K c.t ∧
          ∃ B : Finset (Fin (n + 2)) → Subalgebra K Γ(X, V),
            (∀ S, S.Nonempty → (B S : Set Γ(X, V)) = Set.range (resO (le_biInf_of_le hV S))) ∧
            (∀ S, S.Nonempty → Function.Injective (resO (le_biInf_of_le hV S))) ∧
            (∀ S, S.Nonempty → torusS K (fun k => (ht k).unit) S ≤ B S) ∧
            (∀ S, S.Nonempty → (B S).FG) ∧
            (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K (fun k => (ht k).unit) S) b) ∧
            (∀ j, B (Finset.univ.erase j) ≤ B Finset.univ) ∧
            (∀ r : Γ(X, V), ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b)

end CrystallineSemistableComparison.Pb.LocalCohomologySetup
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

theorem gr_neg_van : ∀ {b : Base} (L : b.Fun) (Q : ObjectProperty (Thick L)) (r : ℤ), r < 0 → ∀ j : ℕ,
    Subsingleton (HU (gr (Φ := thP L) (thFil L) r) Q j) := GlobalTheory.T.thickening_graded_vanish_negative

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

theorem yQ_unit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) (W : X.Opens)
    (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k'), IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := GlobalTheory.T.homogeneous_ratio_isUnit

theorem yQ_mul : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (a b c : Fin m) (W : X.Opens)
    (ha : W ≤ uy i y a) (hb : W ≤ uy i y b) (hc : W ≤ uy i y c),
    (i.appLE _ W hb).hom (yQ y hy a b) * (i.appLE _ W hc).hom (yQ y hy b c) = (i.appLE _ W hc).hom (yQ y hy a c) ∧
    (i.appLE _ W ha).hom (yQ y hy a a) = 1 := GlobalTheory.T.homogeneous_ratio_cocycle

theorem ev_rs : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := GlobalTheory.T.eval_restrict_section

theorem rs_appLE : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)), rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := GlobalTheory.T.restrict_appLE_compat

theorem jacSpan_le : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := GlobalTheory.T.jacobian_span_le_subalgebra

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

theorem cone_transfer : KH.LocGr → KH.PolyTf → KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] {N : ℕ} (i : X ⟶ PSpace K N) (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K),
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, uy i y k)) →
    ∀ (V : X.Opens) (hV : ∀ S : Finset (Fin (n + 2)), V ≤ ⨅ k ∈ S, uy i y k) (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (g : Fin (n + 1) → Γ(X, ⨅ k ∈ Finset.univ, uy i y k)), (∀ k, IsUnit (g k)) →
    ∀ (ĝ : Fin (n + 1) → ∀ T : (capS (wK q i y (n + 2)) Finset.univ).FullSubcategory, T.obj.B),
    (∀ k T (h : InU (⨅ k ∈ Finset.univ, uy i y k) T.obj), Ideal.Quotient.mk _ (ĝ k T) = ev T.obj h (g k)) →
    ∀ (c0 : HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (capS (wK q i y (n + 2)) Finset.univ) (n + 1)),
    Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      (cupListC ((capS (wK q i y (n + 2)) Finset.univ).ι ⋙ thA (smFun X q)) fun k =>
        dlogC (capS (wK q i y (n + 2)) Finset.univ) (n + 2) (ĝ k)) c0 →
    ∀ (ω : ∀ j, HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1))
        (capS (wK q i y (n + 2)) (Finset.univ.erase j)) (n + 1))
      (f : CH.Cn (CH.modF ((capS (wK q i y (n + 2)) Finset.univ).ι ⋙ thA (smFun X q))) n),
    (∀ σ, f σ ∈ (thFil (smFun X q) n).S _) → (∀ σ, CH.d _ n f σ ∈ (thFil (smFun X q) ((n : ℤ) + 1)).S _) →
    Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι) (CH.d _ n f)
      (c0 - ∑ j, ((resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1))
        (capS_univ_le (wK q i y (n + 2)) (Finset.univ.erase j))).pull (n + 1)) (ω j)) →
    ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
      (∀ j, x j ∈ jacSpan (hV (Finset.univ.erase j)) (RingHom.id _) (fun k => D k) id) ∧
      (∀ k, η k ∈ jacSpan (hV Finset.univ) (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
      (Ring.inverse (∏ k, rs (hV Finset.univ) (g k)) * (Matrix.of fun k l => D k (rs (hV Finset.univ) (g l))).det =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k) ∨
        -(Ring.inverse (∏ k, rs (hV Finset.univ) (g k)) * (Matrix.of fun k l => D k (rs (hV Finset.univ) (g l))).det) =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k)) := GlobalTheory.T.projective_chart_affine_coords

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem d_resB {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R)
    {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} (b : CH.Cn (CH.modF (U.ι ⋙ A)) j) :
    CH.d _ j (resB A h b) = resB A h (CH.d _ j b) :=
  (CH.Mor.restrict (CH.modF (U.ι ⋙ A)) (ObjectProperty.ιOfLE h)).d_pullC j b

theorem dpow_mem_pdP' {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (n : ℕ) {x : B} (hx : x ∈ J) :
    δ.dpow n x ∈ pdP δ n :=
  Ideal.subset_span ⟨[(n, x)], by simpa using hx, by simp, by simp⟩

theorem mem_pdP_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have := dpow_mem_pdP' δ 1 hx
  rwa [δ.dpow_one hx] at this

theorem plogK_mem' {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) {x : B} (hx : x ∈ J) :
    plogK δ s x ∈ J :=
  Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (δ.dpow_mem (Nat.succ_ne_zero k) hx)

theorem g_rel {K : Type} [Field K] {X : Scheme.{0}} {N n e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (V W : X.Opens) (hVW : V ≤ W)
    (hW : ∀ b, W ≤ uy i y b) (t : Fin (n + 1) → Γ(X, V)ˣ)
    (ht : ∀ k, (t k : Γ(X, V)) = (i.appLE _ V (hVW.trans (hW 0))).hom (yQ y hy k.succ 0)) (k : Fin (n + 1)) :
    rs hVW ((i.appLE _ W (hW k.succ)).hom (yQ y hy k.castSucc k.succ)) =
      if h : (k : ℕ) = 0 then (((t 0)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) else
        (t ⟨k - 1, by omega⟩ : Γ(X, V)) * (((t k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := by
  have hVb : ∀ b : Fin (n + 2), V ≤ uy i y b := fun b => hVW.trans (hW b)
  set A : Fin (n + 2) → Fin (n + 2) → Γ(X, V) := fun a b =>
    (i.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y b)) V (hVb b)).hom (yQ y hy a b)
    with hAdef
  have hA : ∀ a b c : Fin (n + 2), A a b * A b c = A a c := fun a b c =>
    (yQ_mul i y hy a b c V (hVb a) (hVb b) (hVb c)).1
  have hA1 : ∀ a, A a a = 1 := fun a => (yQ_mul i y hy a a a V (hVb a) (hVb a) (hVb a)).2
  have htA : ∀ k : Fin (n + 1), ((t k : Γ(X, V)ˣ) : Γ(X, V)) = A k.succ 0 := fun k => ht k
  have hinv : ∀ k : Fin (n + 1), A 0 k.succ = (((t k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) := fun k =>
    Units.eq_inv_of_mul_eq_one_left (by rw [htA, hA, hA1])
  have e0 : rs hVW ((i.appLE _ W (hW k.succ)).hom (yQ y hy k.castSucc k.succ)) = A k.castSucc k.succ :=
    rs_appLE i _ hVW (hW k.succ) (yQ y hy k.castSucc k.succ)
  rw [e0]
  by_cases hk : (k : ℕ) = 0
  · have hk0 : k = 0 := Fin.ext hk
    subst hk0
    rw [dif_pos hk]
    exact hinv 0
  · rw [dif_neg hk]
    have e1 : (⟨(k : ℕ) - 1, by omega⟩ : Fin (n + 1)).succ = k.castSucc := Fin.ext (by simp; omega)
    rw [htA, e1, ← hinv k, hA]

set_option maxHeartbeats 800000 in
theorem powK_ne_zero_of (hG : LocalCohomologySetup.GeoSetupP) (hR : LocalCohomologySetup.ResidAlgP) (hL : LocalCohomologySetup.LocExactP)
    {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 := by
  rcases d with _ | n
  · exact oneK_ne_zero q inferInstance
  · intro h0
    obtain ⟨N, i, hci, hiq, hO⟩ := hD
    obtain ⟨e, he, y, hy, hcov, haff, V, hV, cc, hdom, htc, ht, halg, B, hBr, hBi, hBt, hBfg, hBint, hBle, hBfr⟩ :=
      hG q n N i hci hiq
    let _ : Algebra K Γ(X, V) := (strV q V).toAlgebra
    have _ := hdom
    obtain ⟨Dv, hDv⟩ := GlobalTheory.T.exists_dual_derivations_of_coords q V (n + 1) cc

    have hsQ : ∀ T : (wU q i y (n + 2)).FullSubcategory, T.obj.pdPow (n + 2) = ⊥ := fun T => by
      obtain ⟨k, hk, -⟩ := T.property
      exact hk.1
    have hVQ : ∀ T : (wU q i y (n + 2)).FullSubcategory, ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y),
        σ ≫ D.f = V.ι ∧ InU V ((wU q i y (n + 2)).ι.obj T) := fun T => by
      obtain ⟨k, -, W, ⟨j, rfl⟩, hW⟩ := T.property
      obtain ⟨σ, hσ⟩ := wch_mem D N i hO j
      exact ⟨wch i j, σ, hσ, fun x hx => (hW hx).2⟩
    let Λ : CLiftK (wU q i y (n + 2)).ι D :=
      (GlobalTheory.T.exists_cone_lift q D (n + 2)).some.precomp (ObjectProperty.ιOfLE (wU_le q D i y (n + 2) hO))
    obtain ⟨z, hz, hzf, hzc⟩ := hc (n + 2) _ (wU q i y (n + 2)).ι hsQ hVQ Λ
    obtain ⟨hzp, hzp0⟩ := powK_pull q (wU q i y (n + 2)).ι c z hz hzc (n + 1)
    rw [h0, map_zero] at hzp0
    have hzK : z = zK Λ (n + 2) := funext fun σ => hzf σ
    subst hzK
    obtain ⟨b, hb1, hb, hdiff⟩ := hL q D i hO y hy (n + 2) Λ

    let W := wK q i y (n + 2)
    have hsU : ∀ T, (∃ α, W α T) → (thFil (smFun X q) ((n + 2 : ℕ) : ℤ)).S T = ⊥ := by
      rintro T ⟨k, hk, -⟩
      exact hk.1
    have hvanS : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ),
        Subsingleton (HU (sq (thFil (smFun X q) r) (thFil (smFun X q) (r + 1))) (KS q (n + 2) {⨅ k ∈ S, uy i y k}) j) →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hsub
      obtain ⟨h, hbij⟩ := zar_capS q i y (n + 2) S hS r (r + 1) j
      exact hbij.2.subsingleton
    have : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q
    have hvan2 : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (n : ℤ) + 1 < r →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hr
      refine hvanS S hS r j ?_
      exact gr_top_van q (n + 1) _ (haff S hS) (n + 2) r j (by exact_mod_cast hr)
    have hvan1 : ∀ S : Finset (Fin (n + 2)), S.Nonempty → ∀ (r : ℤ) (j : ℕ), (j : ℤ) ≠ r →
        Subsingleton (HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) r) (capS W S) j) := by
      intro S hS r j hjr
      rcases lt_or_ge r 0 with hr | hr
      · exact gr_neg_van _ _ r hr j
      rcases le_or_gt r ((n : ℤ) + 1) with hr' | hr'
      · refine hvanS S hS r j ?_
        obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hr
        exact CrystallineSemistableComparison.Pb.gr_aff q _ (haff S hS) (n + 2) m j (by omega) (by omega)
      · exact hvan2 S hS r j hr'
    have hze : CH.d _ 2 (e • zK Λ (n + 2)) = 0 := by rw [map_nsmul, hz, smul_zero]
    have hz1 : ∀ σ, (e • zK Λ (n + 2)) σ ∈ (thFil (smFun X q) 1).S _ := fun σ => by
      have h := mem_pdP_one ((wU q i y (n + 2)).ι.obj (σ.obj (Fin.last 2))).δ
        (plogK_mem' ((wU q i y (n + 2)).ι.obj (σ.obj (Fin.last 2))).δ (n + 2) (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ))
      exact nsmul_mem h e
    have hzero : ∀ h, (CH.cx _).cls (cupPowC ((ObjectProperty.ι fun T => ∃ α, W α T) ⋙ thA (smFun X q))
        (e • zK Λ (n + 2)) (n + 1)) h = 0 := by
      intro h
      have hsm : cupPowC ((wU q i y (n + 2)).ι ⋙ thA (smFun X q)) (e • zK Λ (n + 2)) (n + 1) =
          ((e : K) ^ (n + 1)) • cupPowC ((wU q i y (n + 2)).ι ⋙ thA (smFun X q)) (zK Λ (n + 2)) (n + 1) := by
        rw [← Nat.cast_smul_eq_nsmul K, cupPowC_smul]
      have hB := ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ hzp).1 hzp0
      refine ((CrystallineSemistableComparison.P.cls_surj _ _).2.1 _ h).2 ?_
      exact hsm ▸ Submodule.smul_mem _ _ hB
    let ℓ : Fin (n + 1) → CH.Cn (CH.modF ((capS W Finset.univ).ι ⋙ thA (smFun X q))) 1 := fun k =>
      resB (thA (smFun X q)) (capS_le_univ W k.castSucc) (b k.castSucc) -
        resB (thA (smFun X q)) (capS_le_univ W k.succ) (b k.succ)
    have hℓcoc : ∀ k, CH.d _ 1 (ℓ k) = 0 := fun k => by
      show CH.d _ 1 (resB _ _ (b k.castSucc) - resB _ _ (b k.succ)) = 0
      rw [map_sub, d_resB, d_resB, ← hb, ← hb]
      exact sub_eq_zero.2 rfl
    have hℓ1 : ∀ k σ, ℓ k σ ∈ (sFil (capS W Finset.univ) 1).S _ := fun k σ => by
      have h1 := hb1 k.castSucc (σ ⋙ ObjectProperty.ιOfLE (capS_le_univ W k.castSucc))
      have h2 := hb1 k.succ (σ ⋙ ObjectProperty.ιOfLE (capS_le_univ W k.succ))
      exact Ideal.sub_mem ((thFil (smFun X q) 1).S (σ.obj (Fin.last 1)).obj) h1 h2
    have hc0' : ∃ c0 : HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (capS W Finset.univ) (n + 1),
        Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS W Finset.univ).ι)
          ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS W Finset.univ).ι)
          (cupListC ((capS W Finset.univ).ι ⋙ (thP (smFun X q)).A) ℓ) c0 := by
      have := rep_cupList (sP (capS W Finset.univ)) (sFil (capS W Finset.univ)) (isFil _) ℓ hℓcoc hℓ1
      rw [Nat.cast_succ] at this
      exact this
    obtain ⟨c0, hc0⟩ := hc0'
    obtain ⟨ω, f, hf, hdf, hrep⟩ := cech_top_rel (thP (smFun X q)) (thFil (smFun X q)) (isFil_th _) (n + 2) n W hsU
      (wK_rel q i y (n + 2)) hvan1 hvan2 (e • zK Λ (n + 2)) hze hz1 b hb1 hb hzero c0 hc0
    have key : ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
        (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
        ((((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k)) := by
      have hKG : KH.LocGr := CrystallineSemistableComparison.Pb.loc_gr
      have hKP : KH.PolyTf := CrystallineSemistableComparison.Pb.poly_tf
      have hKA : KH.GrAff := CrystallineSemistableComparison.Pb.gr_aff
      have hV' : ∀ S : Finset (Fin (n + 2)), V ≤ ⨅ k ∈ S, uy i y k := fun S => le_biInf_of_le hV S
      have hUk : ∀ k, (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) ≤ uy i y k := fun k =>
        biInf_le _ (Finset.mem_univ k)
      let g : Fin (n + 1) → Γ(X, ⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) := fun k =>
        (i.appLE _ _ (hUk k.succ)).hom (yQ y hy k.castSucc k.succ)
      have hg : ∀ k, IsUnit (g k) := fun k => yQ_unit i y hy _ _ _ (hUk _) (hUk _)
      choose ĝ0 hĝ0 hĝd using hdiff
      let ĝ : Fin (n + 1) → ∀ T : (capS W Finset.univ).FullSubcategory, T.obj.B := fun k T =>
        ĝ0 k.castSucc k.succ ⟨T.obj, fun α _ => T.property α (Finset.mem_univ α)⟩
      have hĝ : ∀ k T (h : InU (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), uy i y k) T.obj),
          Ideal.Quotient.mk _ (ĝ k T) = ev T.obj h (g k) := fun k T h => by
        have h1 : InU (uy i y k.succ) T.obj := inU_mono q (hUk k.succ) h
        have e1 := hĝ0 k.castSucc k.succ ⟨T.obj, fun α _ => T.property α (Finset.mem_univ α)⟩ h1
        have e2 := rs_appLE i (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y k.succ))
          (hUk k.succ) le_rfl (yQ y hy k.castSucc k.succ)
        have e3 := ev_rs T.obj (hUk k.succ) h h1
          ((i.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (y k.succ)) (uy i y k.succ)
            le_rfl).hom (yQ y hy k.castSucc k.succ))
        refine e1.trans (e3.symm.trans ?_)
        exact congrArg (ev T.obj h) e2
      have hℓeq : ℓ = fun k => dlogC (capS W Finset.univ) (n + 2) (ĝ k) := funext fun k =>
        congrArg (resB (thA (smFun X q))
          (fun T h α _ => h α (Finset.mem_univ α) : capS W Finset.univ ≤ capS W {k.castSucc, k.succ})) (hĝd k.castSucc k.succ)
      rw [hℓeq] at hc0
      obtain ⟨x, η, hx, hη, heq⟩ := cone_transfer hKG hKP hKA q n i y haff V hV' cc Dv hDv g hg ĝ hĝ c0 hc0 ω f hf hdf hrep
      let tu : Fin (n + 1) → Γ(X, V)ˣ := fun k => (ht k).unit
      let g' : Fin (n + 1) → Γ(X, V) := fun k => if h : (k : ℕ) = 0 then (((tu 0)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) else
        (tu ⟨k - 1, by omega⟩ : Γ(X, V)) * (((tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V))
      have hgt : ∀ k, rs (hV' Finset.univ) (g k) = g' k := fun k =>
        g_rel i y hy V _ (hV' Finset.univ) hUk tu (fun k => by simp only [tu, IsUnit.unit_spec]; exact htc k) k
      have hDvu : ∀ k j, Dv k (tu j) = if k = j then 1 else 0 := fun k j => by simpa [tu] using hDv k j
      have hdr : Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det = (((∏ k, tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) ∨
          Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det = -(((∏ k, tu k)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) :=
        dlog_ratios n tu Dv hDvu
      have hL : Ring.inverse (∏ k, rs (hV' Finset.univ) (g k)) *
          (Matrix.of fun k l => Dv k (rs (hV' Finset.univ) (g l))).det =
          Ring.inverse (∏ k, g' k) * (Matrix.of fun k l => Dv k (g' l)).det := by simp only [hgt]
      rw [hL] at heq
      have hne : ∀ j : Fin (n + 2), (Finset.univ.erase j).Nonempty := fun j =>
        ⟨j.succAbove 0, Finset.mem_erase.2 ⟨Fin.succAbove_ne j 0, Finset.mem_univ _⟩⟩
      have hxm : ∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id := fun j =>
        jacSpan_le (hV' _) (B _) (hBr _ (hne j)) Dv id (hx j)
      have hηm : ∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k) := fun k =>
        jacSpan_le (hV' _) (B _) (hBr _ Finset.univ_nonempty) Dv _ (hη k)
      have hneg : (∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
          (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
          (-(((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
            ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k))) →
          ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
          (∀ j, x j ∈ jacS (B (Finset.univ.erase j)) Dv id) ∧ (∀ k, η k ∈ jacS (B Finset.univ) Dv (Fin.succAbove k)) ∧
          ((((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)) =
            ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * Dv k (η k)) := by
        rintro ⟨x, η, hx, hη, he⟩
        refine ⟨fun j => -x j, fun k => -η k, fun j => (jacS _ Dv id).neg_mem (hx j),
          fun k => (jacS _ Dv _).neg_mem (hη k), ?_⟩
        rw [← neg_neg (((∏ k, (ht k).unit)⁻¹ : Γ(X, V)ˣ) : Γ(X, V)), he]
        simp only [map_neg, mul_neg, Finset.sum_neg_distrib, neg_add]
      rcases hdr with hd | hd <;> rw [hd] at heq <;> rcases heq with he | he
      · exact ⟨x, η, hxm, hηm, he⟩
      · exact hneg ⟨x, η, hxm, hηm, he⟩
      · exact hneg ⟨x, η, hxm, hηm, he⟩
      · exact ⟨x, η, hxm, hηm, by rw [← he, neg_neg]⟩
    obtain ⟨x, η, hx, hη, heq⟩ := key
    refine hR K n Γ(X, V) (fun k => (ht k).unit) (by simpa using halg) Dv (by simpa using hDv) B hBt hBfg hBint
      hBle hBfr x η hx hη heq

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb.LX

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {N : ℕ}

theorem range_sub_awayι {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    Set.range z ⊆ Set.range (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd) := by
  rintro _ ⟨x, rfl⟩
  have hx : z x ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f := h (Set.mem_univ x)
  rw [← Proj.opensRange_awayι _ f hf hd] at hx
  exact hx

def liftA {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f →+* A :=
  (Spec.preimage (IsOpenImmersion.lift (Proj.awayι _ f hf hd) z (range_sub_awayι z hf hd h))).hom

theorem liftA_spec {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) :
    Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z := by
  unfold liftA
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem liftA_unique {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f)
    (φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f →+* A)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι _ f hf hd = z) : φ = liftA z hf hd h := by
  have h1 : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (liftA z hf hd h)) := by
    rw [← cancel_mono (Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd), hφ, liftA_spec]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)

theorem liftA_comp {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A') (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom ρ) ≫ z) ⁻¹ᵁ Proj.basicOpen _ f) :
    liftA (Spec.map (CommRingCat.ofHom ρ) ≫ z) hf hd h' = ρ.comp (liftA z hf hd h) := by
  symm
  apply liftA_unique
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, liftA_spec]

theorem liftA_awayMap {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K} {d d' : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d') (hx : x = f * g)
    (hxd : x ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (d + d')) (hdd : 0 < d + d')
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ x) :
    (liftA z hxd hdd h').comp (HomogeneousLocalization.awayMap _ hg hx) = liftA z hf hd h := by
  apply liftA_unique
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]
  exact liftA_spec z hxd hdd h'

theorem awayToSection_appLE {A : CommRingCat.{0}}
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d)
    (φ : CommRingCat.of (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) ⟶ A)
    (h : ⊤ ≤ (Spec.map φ ≫ Proj.awayι _ f hf hd) ⁻¹ᵁ Proj.basicOpen _ f) :
    Proj.awayToSection _ f ≫ (Spec.map φ ≫ Proj.awayι _ f hf hd).appLE (Proj.basicOpen _ f) ⊤ h ≫
      (Scheme.ΓSpecIso A).hom = φ := by
  obtain ⟨w, hw⟩ : ∃ w, w = Spec.map φ ≫
    (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f hf hd).inv := ⟨_, rfl⟩
  have e1 : Spec.map φ ≫ Proj.awayι _ f hf hd = w ≫ (Proj.basicOpen _ f).ι := by
    rw [hw, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have e2 : w ≫ Proj.basicOpenToSpec _ f = Spec.map φ := by
    rw [hw, ← Proj.basicOpenIsoSpec_hom _ f hf hd, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have e3 : ∀ (z : Spec A ⟶ PSpace K N) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hz : z = w ≫ (Proj.basicOpen _ f).ι),
      z.appLE (Proj.basicOpen _ f) ⊤ h = (Proj.basicOpen _ f).topIso.inv ≫ w.appTop := by
    intro z h hz
    subst hz
    rw [← Scheme.Hom.appLE_comp_appLE w _ _ ⊤ ⊤ (by simp) le_top, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [e3 _ h e1]
  have e4 := Scheme.ΓSpecIso_naturality φ
  rw [← e2, Scheme.Hom.comp_appTop] at e4
  have e5 := Proj.basicOpenToSpec_app_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f
  change (Proj.basicOpenToSpec _ f).appTop = _ at e5
  rw [e5] at e4
  simp only [Category.assoc] at e4
  simpa only [Category.assoc] using (cancel_epi _).1 e4

theorem liftA_eval {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f : MvPolynomial (Fin (N + 1)) K} {d : ℕ} (hf : f ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d)
    (hd : 0 < d) (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    GlobalTheory.Cris.evalAt z (Proj.basicOpen _ f) h ((Proj.awayToSection _ f).hom a) = liftA z hf hd h a := by
  have key : ∀ (z' : Spec (CommRingCat.of A) ⟶ PSpace K N) (h' : ⊤ ≤ z' ⁻¹ᵁ Proj.basicOpen _ f)
      (hz : Spec.map (CommRingCat.ofHom (liftA z hf hd h)) ≫ Proj.awayι _ f hf hd = z'),
      Proj.awayToSection _ f ≫ z'.appLE (Proj.basicOpen _ f) ⊤ h' ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom = CommRingCat.ofHom (liftA z hf hd h) := by
    intro z' h' hz
    subst hz
    exact awayToSection_appLE hf hd _ h'
  exact congrArg (fun ψ => CommRingCat.Hom.hom ψ a) (key z h (liftA_spec z hf hd h))

theorem le_basicOpen_mul {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g : MvPolynomial (Fin (N + 1)) K}
    (hf : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (hg : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ g) :
    ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (f * g) := by
  rw [Proj.basicOpen_mul]
  intro p hp
  exact ⟨hf hp, hg hp⟩

theorem liftA_eval_mul {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N)
    {f g x : MvPolynomial (Fin (N + 1)) K} {d' n : ℕ}
    (hg : g ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K d') (hx : x = f * g)
    (hxd : x ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K n) (hn : 0 < n)
    (h : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ f) (h' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ x)
    (a : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) f) :
    GlobalTheory.Cris.evalAt z (Proj.basicOpen _ f) h ((Proj.awayToSection _ f).hom a) =
      liftA z hxd hn h' (HomogeneousLocalization.awayMap _ hg hx a) := by
  rw [← liftA_eval]
  have e : Proj.awayToSection _ f ≫ z.appLE (Proj.basicOpen _ f) ⊤ h =
      CommRingCat.ofHom (HomogeneousLocalization.awayMap _ hg hx) ≫ Proj.awayToSection _ x ≫
        z.appLE (Proj.basicOpen _ x) ⊤ h' := by
    rw [← Category.assoc, Proj.awayMap_awayToSection, Category.assoc, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (CommRingCat.Hom.hom ψ a)) e

def yx {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1))
    (k : Fin m) : ChartR K N j :=
  HomogeneousLocalization.Away.mk _ (X_mem K N j) e (y k)
    (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k))

theorem liftA_yx_isUnit {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1)) (k : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hk : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (y k)) :
    IsUnit (liftA z (X_mem K N j) one_pos hj (yx y hy j k)) := by
  have hyk := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have hxd : MvPolynomial.X j * y k ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e) :=
    SetLike.mul_mem_graded (X_mem K N j) hyk
  have hx := le_basicOpen_mul z hj hk
  rw [← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx, RingHom.comp_apply]
  apply IsUnit.map
  have hX : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K) ^ (1 + e) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 • (1 + e)) := by
    simpa using SetLike.pow_mem_graded (1 + e) (X_mem K N j)
  refine IsUnit.of_mul_eq_one (HomogeneousLocalization.Away.mk _ hxd 1 _ hX) ?_
  apply HomogeneousLocalization.val_injective
  unfold yx
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, Localization.mk_mul,
    ← Localization.mk_one, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, Submonoid.coe_one]
  ring

theorem liftA_yx_change {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j j' : Fin (N + 1)) (k : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hj' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j')) :
    liftA z (X_mem K N j) one_pos hj (yx y hy j k) =
      liftA z (X_mem K N j') one_pos hj' (yx y hy j' k) * liftA z (X_mem K N j) one_pos hj (ratio K N j j') ^ e := by
  have hxd : (MvPolynomial.X j * MvPolynomial.X j' : MvPolynomial (Fin (N + 1)) K) ∈
      MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + 1) :=
    SetLike.mul_mem_graded (X_mem K N j) (X_mem K N j')
  have hx := le_basicOpen_mul z hj hj'
  rw [← liftA_awayMap z (X_mem K N j) one_pos (X_mem K N j') rfl hxd (by omega) hj hx,
    ← liftA_awayMap z (X_mem K N j') one_pos (X_mem K N j) (mul_comm _ _) hxd (by omega) hj' hx]
  simp only [RingHom.comp_apply]
  rw [← map_pow, ← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  unfold yx ratio
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow]
  ring

theorem liftA_yx_quot {A : Type} [CommRing A] (z : Spec (CommRingCat.of A) ⟶ PSpace K N) {m e : ℕ}
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (j : Fin (N + 1)) (k k' : Fin m)
    (hj : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X j)) (hk' : ⊤ ≤ z ⁻¹ᵁ Proj.basicOpen _ (y k')) :
    liftA z (X_mem K N j) one_pos hj (yx y hy j k) =
      liftA z (X_mem K N j) one_pos hj (yx y hy j k') *
        GlobalTheory.Cris.evalAt z (Proj.basicOpen _ (y k')) hk'
          ((Proj.awayToSection _ (y k')).hom
            (HomogeneousLocalization.Away.mk _ ((MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')) 1 (y k)
              (by simpa using (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)))) := by
  have hyk := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hxd : MvPolynomial.X j * y k' ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K (1 + e) :=
    SetLike.mul_mem_graded (X_mem K N j) hyk
  have hx := le_basicOpen_mul z hj hk'
  rw [liftA_eval_mul z (X_mem K N j) (mul_comm _ _) hxd (by omega) hk' hx,
    ← liftA_awayMap z (X_mem K N j) one_pos hyk rfl hxd (by omega) hj hx]
  simp only [RingHom.comp_apply]
  rw [← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  unfold yx
  rw [HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul]
  ring

end CrystallineSemistableComparison.Pb.LX
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.ConeZcls (ub ub_mul ub_nat ub_isUnit exists_unit_lift pt_map)

namespace CrystallineSemistableComparison.Pb.LX

attribute [local instance] MvPolynomial.gradedAlgebra

section Pts
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem inU_map_c {V : X.Opens} {T T' : Thick (smFun X q)} (f : T ⟶ T') (h : InU V T) : InU V T' := by
  intro x _
  have e := pt_map f
  have hx : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) x) ∈ pt T ⁻¹ᵁ V := h (Set.mem_univ _)
  change (pt T') x ∈ V
  rw [← e]
  exact hx

theorem inU_inf_left {V W : X.Opens} {T : Thick (smFun X q)} (h : InU (V ⊓ W) T) : InU V T :=
  inU_mono q inf_le_left h

theorem inU_inf_right {V W : X.Opens} {T : Thick (smFun X q)} (h : InU (V ⊓ W) T) : InU W T :=
  inU_mono q inf_le_right h

end Pts

variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {N : ℕ}
  (i : X ⟶ PSpace K N) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (s : ℕ)

theorem wK_tf {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : TF 1 s T := h.1

theorem wK_uy {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : InU (uy i y k) T := by
  obtain ⟨-, V, ⟨j, rfl⟩, hV⟩ := h
  exact inU_inf_left hV

theorem wK_wch {k : Fin m} {T : Thick (smFun X q)} (h : wK q i y s k T) : ∃ j, InU (wch i j) T := by
  obtain ⟨-, V, ⟨j, rfl⟩, hV⟩ := h
  exact ⟨j, inU_inf_right hV⟩

theorem wK_le_wU (k : Fin m) : wK q i y s k ≤ wU q i y s := fun _ h => ⟨k, h⟩

theorem wU_wch {T : Thick (smFun X q)} (h : wU q i y s T) : ∃ j, InU (wch i j) T := by
  obtain ⟨k, hk⟩ := h
  exact wK_wch i y s hk

def lj (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) : ChartR K N j →+* T.B ⧸ T.J :=
  liftA (pt T ≫ i) (X_mem K N j) one_pos h

theorem lj_spec (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    pt T ≫ i = Spec.map (CommRingCat.ofHom (lj i T j h)) ≫ chart K N j :=
  (liftA_spec (pt T ≫ i) (X_mem K N j) one_pos h).symm

def az (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    Spec (CommRingCat.of (T.B ⧸ T.J)) ⟶ pullback i (chart K N j) :=
  pullback.lift (pt T) (Spec.map (CommRingCat.ofHom (lj i T j h))) (lj_spec i T j h)

theorem lj_comp {T T' : Thick (smFun X q)} (f : T ⟶ T') (j : Fin (N + 1)) (h : InU (wch i j) T) (h' : InU (wch i j) T') :
    lj i T' j h' = (Ideal.quotientMap T'.J f.φ f.hle).comp (lj i T j h) := by
  have e : pt T' ≫ i = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) ≫ (pt T ≫ i) := by
    rw [← Category.assoc, pt_map f]
  unfold lj
  have key := liftA_comp (Ideal.quotientMap T'.J f.φ f.hle) (pt T ≫ i) (X_mem K N j) one_pos h (e ▸ h')
  refine Eq.trans ?_ key
  congr 1

section O1
variable {D : E.LineData X}

def sO (hD : IsTautologicalLineAt D N i) (j : Fin (N + 1)) : pullback i (chart K N j) ⟶ D.Y := hD.2.choose j

theorem sO_f (hD : IsTautologicalLineAt D N i) (j : Fin (N + 1)) : sO i hD j ≫ D.f = pullback.fst _ _ :=
  hD.2.choose_spec.choose j

theorem sO_u (hD : IsTautologicalLineAt D N i) {V : Scheme.{0}} (j k : Fin (N + 1)) (a : V ⟶ pullback i (chart K N j))
    (b : V ⟶ pullback i (chart K N k)) (h : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _)
    (h' : (a ≫ sO i hD j) ≫ D.f = (b ≫ sO i hD k) ≫ D.f) :
    ((D.u (a ≫ sO i hD j) (b ≫ sO i hD k) h' : Γ(V, ⊤)ˣ) : Γ(V, ⊤)) =
      (a ≫ pullback.snd _ _).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR K N j))).inv.hom (ratio K N j k)) :=
  hD.2.choose_spec.choose_spec V j k a b h

theorem ub_congr {A : Type} [CommRing A] {a a' b b' : Spec (CommRingCat.of A) ⟶ D.Y} (ha : a = a') (hb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) : ub (D := D) a b h = ub (D := D) a' b' h' := by
  subst ha hb; rfl

theorem az_f (hD : IsTautologicalLineAt D N i) (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    (az i T j h ≫ sO i hD j) ≫ D.f = pt T := by
  rw [Category.assoc, sO_f]
  exact pullback.lift_fst _ _ _

theorem az_f' (hD : IsTautologicalLineAt D N i) (T : Thick (smFun X q)) (j : Fin (N + 1)) (h : InU (wch i j) T) :
    az i T j h ≫ sO i hD j ≫ D.f = pt T := by
  rw [sO_f]
  exact pullback.lift_fst _ _ _

def jc (c : (wU q i y s).FullSubcategory) : Fin (N + 1) := (wU_wch i y s c.property).choose

theorem hjc (c : (wU q i y s).FullSubcategory) : InU (wch i (jc i y s c)) c.obj := (wU_wch i y s c.property).choose_spec

def AU (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (c : (wU q i y s).FullSubcategory) : (c.obj.B ⧸ c.obj.J)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (c.obj.B ⧸ c.obj.J))).hom.hom.toMonoidHom
    (D.u (az i c.obj (jc i y s c) (hjc i y s c) ≫ sO i hD (jc i y s c)) (Λ.p c) ((az_f i hD _ _ _).trans (Λ.hp c).symm))

def μ (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory) : c.obj.B ⧸ c.obj.J :=
  lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k) *
    (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J)

theorem μ_isUnit (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) : IsUnit (μ i y hy s hD Λ k c) :=
  (liftA_yx_isUnit (pt c.obj ≫ i) y hy _ k (hjc i y s c) hk).mul (Units.isUnit _)

def vv (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) : c.obj.Bˣ :=
  (exists_unit_lift c.obj _ (μ_isUnit i y hy s hD Λ k c hk)).choose

theorem vv_spec (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) (c : (wU q i y s).FullSubcategory)
    (hk : InU (uy i y k) c.obj) :
    Ideal.Quotient.mk c.obj.J ((vv i y hy s hD Λ k c hk : c.obj.Bˣ) : c.obj.B) = μ i y hy s hD Λ k c :=
  (exists_unit_lift c.obj _ (μ_isUnit i y hy s hD Λ k c hk)).choose_spec

end O1

section E
variable {D : E.LineData X}

theorem gamma_specMap {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      ((Spec.map (CommRingCat.ofHom ψ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ψ r := by
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((Spec.map (CommRingCat.ofHom ψ)).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom).hom _ = _
  rw [e]
  simp

theorem eps_mem (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D) (k : Fin m) {c c' : (wU q i y s).FullSubcategory}
    (φ : c ⟶ c') (hk : InU (uy i y k) c.obj) (hk' : InU (uy i y k) c'.obj) :
    (((show c'.obj.Bˣ from Λ.w φ) ^ e * vv i y hy s hD Λ k c' hk' *
        (Units.map (show c.obj ⟶ c'.obj from (wU q i y s).ι.map φ).φ.toMonoidHom (vv i y hy s hD Λ k c hk))⁻¹ :
          c'.obj.Bˣ) : c'.obj.B) - 1 ∈ c'.obj.J := by
  set f : c.obj ⟶ c'.obj := (wU q i y s).ι.map φ with hf
  set Q := Ideal.quotientMap c'.obj.J f.φ f.hle with hQ
  have hj : InU (wch i (jc i y s c)) c.obj := hjc i y s c
  have hj' : InU (wch i (jc i y s c')) c'.obj := hjc i y s c'
  have hjT : InU (wch i (jc i y s c)) c'.obj := inU_map_c f hj
  have hpt : Spec.map (CommRingCat.ofHom Q) ≫ pt c.obj = pt c'.obj := pt_map f

  have h1 : (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [Category.assoc, Λ.hp, Λ.hp]; exact hpt
  have ew : Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) =
      ub (D := D) (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) (Λ.p c') h1 := Λ.hw φ h1

  have h2 : (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c))) ≫ D.f =
      (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) ≫ D.f := by
    simp only [Category.assoc, az_f']
    rw [Λ.hp]
    rfl
  have eA : Q (((AU i y s hD Λ c : (c.obj.B ⧸ c.obj.J)ˣ)) : c.obj.B ⧸ c.obj.J) =
      ub (D := D) (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c)))
        (Spec.map (CommRingCat.ofHom Q) ≫ Λ.p c) h2 :=
    (ub_nat Q _ _ _ h2).symm

  have h3 : (Spec.map (CommRingCat.ofHom Q) ≫ (az i c.obj _ hj ≫ sO i hD (jc i y s c))) ≫ D.f =
      (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f := by
    simp only [Category.assoc, az_f']
    exact hpt
  have h4 : (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f = Λ.p c' ≫ D.f := by
    rw [az_f, Λ.hp]
    rfl
  have hcoc : ub (D := D) _ _ h2 * ub (D := D) _ _ h1 = ub (D := D) _ _ h3 * ub (D := D) _ _ h4 := by
    rw [ub_mul, ub_mul]

  have h5 : (Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ pullback.fst _ _ = az i c'.obj _ hj' ≫ pullback.fst _ _ := by
    rw [Category.assoc]
    unfold az
    rw [pullback.lift_fst, pullback.lift_fst, hpt]
  have h3' : ((Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ sO i hD (jc i y s c)) ≫ D.f =
      (az i c'.obj _ hj' ≫ sO i hD (jc i y s c')) ≫ D.f := by
    rw [Category.assoc]; exact h3
  have eR : ub (D := D) _ _ h3 = lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) := by
    rw [ub_congr (Category.assoc _ _ _).symm rfl h3 h3']
    unfold ub
    rw [sO_u i hD _ _ _ _ h5 h3']
    have e6 : (Spec.map (CommRingCat.ofHom Q) ≫ az i c.obj _ hj) ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (lj i c'.obj _ hjT)) := by
      rw [Category.assoc]
      unfold az
      rw [pullback.lift_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun ψ => Spec.map (CommRingCat.ofHom ψ)) (lj_comp i f _ hj hjT).symm
    rw [e6]
    exact gamma_specMap _ _

  have hY : lj i c'.obj _ hjT (yx y hy (jc i y s c) k) =
      lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) ^ e :=
    liftA_yx_change (pt c'.obj ≫ i) y hy (jc i y s c) (jc i y s c') k hjT hj'
  have eY : Q (lj i c.obj _ hj (yx y hy (jc i y s c) k)) = lj i c'.obj _ hjT (yx y hy (jc i y s c) k) :=
    (RingHom.congr_fun (lj_comp i f _ hj hjT) _).symm

  have key : Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) ^ e * μ i y hy s hD Λ k c' =
      Q (μ i y hy s hD Λ k c) := by
    set U := Units.map Q.toMonoidHom (AU i y s hD Λ c) with hU
    have hUv : (U : c'.obj.B ⧸ c'.obj.J) = ub (D := D) _ _ h2 := eA
    set A' := AU i y s hD Λ c' with hA'
    have hA'v : (A' : c'.obj.B ⧸ c'.obj.J) = ub (D := D) _ _ h4 := rfl
    set W := Ideal.Quotient.mk c'.obj.J ((show c'.obj.Bˣ from Λ.w φ) : c'.obj.B) with hWdef
    set R := lj i c'.obj _ hjT (ratio K N (jc i y s c) (jc i y s c')) with hR
    have hc : (U : c'.obj.B ⧸ c'.obj.J) * W = R * A' := by
      rw [hUv, hA'v, ew, ← eR]; exact hcoc
    have hW : W = ((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) * (R * A') := by
      rw [← hc, ← mul_assoc, Units.inv_mul, one_mul]
    have hQμ : Q (μ i y hy s hD Λ k c) = lj i c'.obj _ hjT (yx y hy (jc i y s c) k) *
        (((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J)) ^ e := by
      unfold μ
      rw [map_mul, eY, Units.val_pow_eq_pow_val, map_pow]
      rfl
    rw [hQμ]
    unfold μ
    rw [← hA', hY, hW, Units.val_pow_eq_pow_val]
    have hA : (A' : c'.obj.B ⧸ c'.obj.J) ^ e * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e = 1 := by
      rw [← mul_pow, Units.mul_inv, one_pow]
    calc (((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) * (R * A')) ^ e *
          (lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e)
        = lj i c'.obj _ hj' (yx y hy (jc i y s c') k) * R ^ e * ((U⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e *
          ((A' : c'.obj.B ⧸ c'.obj.J) ^ e * ((A'⁻¹ : (c'.obj.B ⧸ c'.obj.J)ˣ) : c'.obj.B ⧸ c'.obj.J) ^ e) := by ring
      _ = _ := by rw [hA, mul_one]

  have hv := vv_spec i y hy s hD Λ k c hk
  have hv' := vv_spec i y hy s hD Λ k c' hk'
  have hfv : Ideal.Quotient.mk c'.obj.J
      ((Units.map f.φ.toMonoidHom (vv i y hy s hD Λ k c hk) : c'.obj.Bˣ) : c'.obj.B) = Q (μ i y hy s hD Λ k c) := by
    rw [← hv]; rfl
  have hinv : Ideal.Quotient.mk c'.obj.J
      (((Units.map f.φ.toMonoidHom (vv i y hy s hD Λ k c hk))⁻¹ : c'.obj.Bˣ) : c'.obj.B) * Q (μ i y hy s hD Λ k c) = 1 := by
    rw [← hfv, ← map_mul, Units.inv_mul, map_one]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero, Units.val_mul, Units.val_mul,
    Units.val_pow_eq_pow_val, map_mul, map_mul, map_pow, hv', key, mul_comm]
  exact hinv

end E

end CrystallineSemistableComparison.Pb.LX
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.LX

variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C]
  {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def epsE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').Bˣ :=
  Λ.w φ ^ e * v c' * (Units.map (g.map φ).φ.toMonoidHom (v c))⁻¹

def bE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) : CH.Cn (g ⋙ O (smFun X q)) 1 :=
  fun τ => (show (g.obj (τ.obj (Fin.last 1))).B from
    plogK (g.obj (τ.obj (Fin.last 1))).δ s (((epsE Λ v e (τ.map' 0 1) : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
      (g.obj (τ.obj (Fin.last 1))).B) - 1))

theorem grpE_add {G : Type} [AddCommGroup G] (a b c x y z : G) (e : ℕ) :
    e • a + y + -z + (e • b + x + -y) + -(e • c + x + -z) = e • (a + b + -c) := by
  simp only [smul_add, smul_neg]; abel

theorem grpE {G : Type} [CommGroup G] (a b c x y z : G) (e : ℕ) :
    a ^ e * y * z⁻¹ * (b ^ e * x * y⁻¹) * (c ^ e * x * z⁻¹)⁻¹ = (a * b * c⁻¹) ^ e :=
  @grpE_add (Additive G) _ a b c x y z e

theorem grpS_add {G : Type} [AddCommGroup G] (a x x' y y' : G) :
    (a + x + -y) + -(a + x' + -y') = (x + -x') + -(y + -y') := by abel

theorem grpS {G : Type} [CommGroup G] (a x x' y y' : G) :
    (a * x * y⁻¹) * (a * x' * y'⁻¹)⁻¹ = (x * x'⁻¹) * (y * y'⁻¹)⁻¹ :=
  @grpS_add (Additive G) _ a x x' y y'

theorem plog_pow [CharZero K] (T : Thick (smFun X q)) (s : ℕ) (hs : T.pdPow s = ⊥) (a : T.Bˣ)
    (ha : (a : T.B) - 1 ∈ T.J) (n : ℕ) :
    ((a ^ n : T.Bˣ) : T.B) - 1 ∈ T.J ∧
      plogK T.δ s (((a ^ n : T.Bˣ) : T.B) - 1) = n • plogK T.δ s ((a : T.B) - 1) := by
  induction n with
  | zero => simp [GlobalTheory.CompanionTheory.ConeZcls.plogK_zero, T.J.zero_mem]
  | succ n ih =>
    rw [pow_succ]
    refine ⟨GlobalTheory.CompanionTheory.ConeZcls.mul_sub_mem T _ _ ih.1 ha, ?_⟩
    rw [GlobalTheory.CompanionTheory.ConeZcls.plog_mul T s hs _ _ ih.1 ha, ih.2, succ_nsmul]

theorem epsE_rr (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂)
    (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ) :
    Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) * epsE Λ v e ψ * (epsE Λ v e χ)⁻¹ =
      GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ ^ e := by
  subst hχ
  have h : Units.map (g.map (φ ≫ ψ)).φ.toMonoidHom (v c₀) =
      Units.map (g.map ψ).φ.toMonoidHom (Units.map (g.map φ).φ.toMonoidHom (v c₀)) := by
    rw [g.map_comp]; rfl
  unfold epsE GlobalTheory.CompanionTheory.ConeZcls.rr
  rw [h]
  simp only [map_mul, map_inv, map_pow]
  exact grpE _ _ _ _ _ _ e

def lE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').B :=
  plogK (g.obj c').δ s (((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1)

theorem log_rr [CharZero K] (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ)
    (hr : ((GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J) :
    e • plogK (g.obj c₂).δ s (((GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1) =
      (g.map ψ).φ (lE Λ v e s φ) + lE Λ v e s ψ - lE Λ v e s χ := by
  have e0 := hε φ
  have e1 := hε ψ
  have e2 := hε χ
  have e0' : ((Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J := by
    have := (g.map ψ).hle e0
    simpa using this
  have hm : plogK (g.obj c₂).δ s (((Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) : (g.obj c₂).Bˣ) :
      (g.obj c₂).B) - 1) = (g.map ψ).φ (lE Λ v e s φ) := by
    unfold lE
    rw [GlobalTheory.CompanionTheory.ConeZcls.plogK_map (g.map ψ) s e0]
    simp
  rw [← (plog_pow (g.obj c₂) s (hs _) _ hr e).2, ← epsE_rr Λ v e φ ψ χ hχ,
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ (GlobalTheory.CompanionTheory.ConeZcls.mul_sub_mem _ _ _ e0' e1)
      (GlobalTheory.CompanionTheory.ConeZcls.inv_sub _ _ e2),
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ e0' e1, GlobalTheory.CompanionTheory.ConeZcls.plog_inv _ s (hs _) _ e2, hm]
  unfold lE
  ring

theorem epsE_div (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c c' : C} (φ : c ⟶ c') :
    epsE Λ v e φ * (epsE Λ v' e φ)⁻¹ =
      (v c' * (v' c')⁻¹) * (Units.map (g.map φ).φ.toMonoidHom (v c * (v' c)⁻¹))⁻¹ := by
  unfold epsE
  simp only [map_mul, map_inv]
  exact grpS _ _ _ _ _

theorem lE_sub [CharZero K] (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    {c c' : C} (φ : c ⟶ c')
    (e1 : ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (e2 : ((epsE Λ v' e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J) :
    lE Λ v e s φ - lE Λ v' e s φ =
      plogK (g.obj c').δ s (((v c' * (v' c')⁻¹ : (g.obj c').Bˣ) : (g.obj c').B) *
        Ring.inverse ((g.map φ).φ (((v c * (v' c)⁻¹ : (g.obj c).Bˣ) : (g.obj c).B))) - 1) := by
  have hR : Ring.inverse ((g.map φ).φ (((v c * (v' c)⁻¹ : (g.obj c).Bˣ) : (g.obj c).B))) =
      (((Units.map (g.map φ).φ.toMonoidHom (v c * (v' c)⁻¹))⁻¹ : (g.obj c').Bˣ) : (g.obj c').B) := by
    rw [← Ring.inverse_unit]; rfl
  unfold lE
  rw [hR, ← Units.val_mul, ← epsE_div Λ v v' e φ,
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ e1 (GlobalTheory.CompanionTheory.ConeZcls.inv_sub _ _ e2),
    GlobalTheory.CompanionTheory.ConeZcls.plog_inv _ s (hs _) _ e2, sub_eq_add_neg]

theorem zK_smul_eq_d [CharZero K] (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J) :
    e • zK Λ s = CH.d _ 1 (bE Λ v e s) := by
  funext σ
  have hr : ((GlobalTheory.CompanionTheory.ConeZcls.rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) : (g.obj (σ.obj (Fin.last 2))).Bˣ) :
      (g.obj (σ.obj (Fin.last 2))).B) - 1 ∈ (g.obj (σ.obj (Fin.last 2))).J := GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ
  have key := log_rr Λ v e s hs hε (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (GlobalTheory.CompanionTheory.ConeZcls.composable_arrows_map_zero_two σ) hr
  have h0 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 0 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 0 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from lE Λ v e s (σ.map' 1 2)) :=
    GlobalTheory.CompanionTheory.ConeZcls.map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h1 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 1 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 1 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from lE Λ v e s (σ.map' 0 2)) :=
    GlobalTheory.CompanionTheory.ConeZcls.map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h2 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 2 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 2 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from (g.map (σ.map' 1 2)).φ (lE Λ v e s (σ.map' 0 1))) := rfl
  have hd : CH.d (g ⋙ O (smFun X q)) 1 (bE Λ v e s) σ =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast i σ)).hom
        (bE Λ v e s (GlobalTheory.CatH.face i σ)) := rfl
  rw [Pi.smul_apply, hd, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_pow, one_pow]
  rw [h0, h1, h2]
  refine key.trans ?_
  have fin : ∀ a b c : (g.obj (σ.obj (Fin.last 2))).B, a + b - c = b + -c + a := fun a b c => by abel
  exact fin _ _ _

theorem bE_mem (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (τ : ComposableArrows C 1) : (show (g.obj (τ.obj (Fin.last 1))).B from bE Λ v e s τ) ∈ (g.obj (τ.obj (Fin.last 1))).J := by
  change plogK (g.obj (τ.obj (Fin.last 1))).δ s (((epsE Λ v e (τ.map' 0 1) : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
    (g.obj (τ.obj (Fin.last 1))).B) - 1) ∈ _
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ((g.obj (τ.obj (Fin.last 1))).δ.dpow_mem (Nat.succ_ne_zero k)
    (hε (τ.map' 0 1)))

theorem bE_sub [CharZero K] (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (hε' : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v' e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (τ : ComposableArrows C 1) :
    (show (g.obj (τ.obj (Fin.last 1))).B from bE Λ v e s τ - bE Λ v' e s τ) =
      plogK (g.obj (τ.obj (Fin.last 1))).δ s
        (((v (τ.obj (Fin.last 1)) * (v' (τ.obj (Fin.last 1)))⁻¹ : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
            (g.obj (τ.obj (Fin.last 1))).B) *
          Ring.inverse (show (g.obj (τ.obj (Fin.last 1))).B from (g.map (τ.map' 0 1)).φ
            (((v (τ.obj 0) * (v' (τ.obj 0))⁻¹ : (g.obj (τ.obj 0)).Bˣ) : (g.obj (τ.obj 0)).B))) - 1) :=
  lE_sub Λ v v' e s hs (τ.map' 0 1) (hε (τ.map' 0 1)) (hε' (τ.map' 0 1))

end CrystallineSemistableComparison.Pb.LX
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

namespace LX

section Fam
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {N : ℕ} {D : E.LineData X}
  (i : X ⟶ PSpace K N) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (s : ℕ)
  (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D)

def vV (k : Fin m) (V : ObjectProperty (Thick (smFun X q))) (hV : V ≤ wU q i y s) (hk : ∀ T, V T → InU (uy i y k) T) :
    ∀ c : V.FullSubcategory, ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c).Bˣ :=
  fun c => vv i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).obj c) (hk _ c.property)

theorem vV_eps (k : Fin m) (V : ObjectProperty (Thick (smFun X q))) (hV : V ≤ wU q i y s)
    (hk : ∀ T, V T → InU (uy i y k) T) {c c' : V.FullSubcategory} (φ : c ⟶ c') :
    ((epsE (Λ.precomp (ObjectProperty.ιOfLE hV)) (vV i y hy s hD Λ k V hV hk) e φ :
        ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').Bˣ) : ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').B) - 1 ∈
      ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').J :=
  eps_mem i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).map φ) (hk _ c.property) (hk _ c'.property)

end Fam

theorem evalAt_comp_appLE {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Spec (CommRingCat.of A) ⟶ Y) (f : Y ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ U)) (h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (a : Γ(Z, U)) :
    GlobalTheory.Cris.evalAt (x ≫ f) U h' a = GlobalTheory.Cris.evalAt x (f ⁻¹ᵁ U) h (f.appLE U (f ⁻¹ᵁ U) le_rfl a) := by
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE x f U (f ⁻¹ᵁ U) ⊤ le_rfl h]
  rfl

theorem mem_pdP_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have h := dpow_mem_pdP δ 1 hx
  rwa [δ.dpow_one hx] at h

theorem mem_thFil_one {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {T : Thick (smFun X q)} {x : T.B} (hx : x ∈ T.J) :
    (show (thA (smFun X q)).obj T from x) ∈ (thFil (smFun X q) 1).S T :=
  mem_pdP_one T.δ hx

end LX

open LX

theorem firstChern_local_exact [CharZero K] (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (i : X ⟶ PSpace K N)
    (hD : IsTautologicalLineAt D N i) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e)
    (s : ℕ) (Λ : CLiftK (ObjectProperty.ι fun T : Thick (smFun X q) => ∃ k, wK q i y s k T) D) :
    ∃ b : ∀ k, CH.Cn (CH.modF ((wK q i y s k).ι ⋙ thA (smFun X q))) 1,
      (∀ k σ, b k σ ∈ (thFil (smFun X q) 1).S _) ∧
      (∀ k, resB (thA (smFun X q)) (fun T h => ⟨k, h⟩ : wK q i y s k ≤ fun T : Thick (smFun X q) => ∃ k', wK q i y s k' T)
        (e • zK Λ s) = CH.d _ 1 (b k)) ∧
      ∀ k k', ∃ ĝ : ∀ T : (capS (wK q i y s) {k, k'}).FullSubcategory, T.obj.B,
        (∀ T (h : InU (uy i y k') T.obj),
          Ideal.Quotient.mk _ (ĝ T) = ev T.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k'))) ∧
        resB (thA (smFun X q)) (fun T h => h k (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k) (b k) -
          resB (thA (smFun X q)) (fun T h => h k' (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k') (b k') =
          dlogC (capS (wK q i y s) {k, k'}) s ĝ := by
  classical
  have hsk : ∀ k (c : (wK q i y s k).FullSubcategory), c.obj.pdPow s = ⊥ := fun k c => (wK_tf i y s c.property).1
  refine ⟨fun k => bE (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s, ?_, ?_, ?_⟩
  · intro k σ
    exact mem_thFil_one (bE_mem (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s
      (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) σ)
  · intro k
    exact zK_smul_eq_d (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s (hsk k)
      (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h))
  · intro k k'
    have hkk : k ∈ ({k, k'} : Finset (Fin m)) := by simp
    have hkk' : k' ∈ ({k, k'} : Finset (Fin m)) := by simp
    have hcU : capS (wK q i y s) {k, k'} ≤ wU q i y s := fun T h => wK_le_wU i y s k T (h k hkk)
    have hc1 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k) T := fun T h => wK_uy i y s (h k hkk)
    have hc2 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k') T := fun T h => wK_uy i y s (h k' hkk')
    refine ⟨fun T => (show T.obj.B from ((vV i y hy s hD Λ k _ hcU hc1 T * (vV i y hy s hD Λ k' _ hcU hc2 T)⁻¹ :
        ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).Bˣ) : ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).B)),
      ?_, ?_⟩
    · intro T h
      set c : (wU q i y s).FullSubcategory := (ObjectProperty.ιOfLE hcU).obj T
      have h1 := vv_spec i y hy s hD Λ k c (hc1 _ T.property)
      have h2 := vv_spec i y hy s hD Λ k' c (hc2 _ T.property)
      have hq : lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k) =
          lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
            ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) := by
        refine (liftA_yx_quot (pt c.obj ≫ i) y hy (jc i y s c) k k' (hjc i y s c) h).trans ?_
        congr 1
        exact evalAt_comp_appLE (pt c.obj) i _ h h _
      change Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k c (hc1 _ T.property) *
        (vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) = _
      rw [Units.val_mul, map_mul, h1]
      have h3 : Ideal.Quotient.mk c.obj.J ((vv i y hy s hD Λ k' c (hc2 _ T.property) : c.obj.Bˣ) : c.obj.B) *
          Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [h2] at h3
      unfold μ at h3 ⊢
      rw [hq]
      calc lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
              ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) *
              (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J) *
            Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)
          = ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) *
            (lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
              (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J) *
            Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) := by ring
        _ = _ := by rw [h3, mul_one]; rfl
    · funext τ
      exact bE_sub (Λ.precomp (ObjectProperty.ιOfLE hcU)) (vV i y hy s hD Λ k _ hcU hc1) (vV i y hy s hD Λ k' _ hcU hc2)
        e s (fun c => (wK_tf i y s (c.property k hkk)).1)
        (vV_eps i y hy s hD Λ k _ hcU hc1) (vV_eps i y hy s hD Λ k' _ hcU hc2) τ

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Pb

theorem powK_ne_zero_main {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 :=
  powK_ne_zero_of (by intro K _ _ X q _ n _ N i hci hiq; exact geo_setup q n N i hci hiq) resid_alg
    (by intro K _ X N _ q D i hD m e y hy s Λ; exact firstChern_local_exact q D i hD y hy s Λ) q d D hD c hc

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem isProper_of_isO1 {R : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R}
    {D : E.LineData X} (hD : IsTautologicalLine p D) : IsProper p := by
  obtain ⟨N, i, hi, hip, -⟩ := hD
  exact GlobalTheory.CommonModel.isProper_of_isProjOver ⟨N, i, hi, hip⟩

theorem cls_congr {R : Type} [CommRing R] (K : Cx.{1} R) {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0)
    (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst h; rfl

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

omit [CharZero K] in
theorem ks_mono (𝒱 : Set X.Opens) {s S : ℕ} (h : s ≤ S) : KS q s 𝒱 ≤ KS q S 𝒱 := fun T hT =>
  ⟨⟨show pdP T.δ S = ⊥ from eq_bot_iff.2 ((dividedPowerFiltration_anti T.δ h).trans (le_of_eq hT.1.1)), hT.1.2⟩, hT.2⟩

omit [CharZero K] in
theorem ks_pd (𝒱 : Set X.Opens) (s : ℕ) (c : (KS q s 𝒱).FullSubcategory) : ((KS q s 𝒱).ι.obj c).pdPow s = ⊥ :=
  c.property.1.1

omit [CharZero K] in
theorem ks_sec (D : E.LineData X) (s : ℕ) (c : (KS q s (𝒱D D)).FullSubcategory) :
    ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V ((KS q s (𝒱D D)).ι.obj c) := by
  obtain ⟨-, V, ⟨σ, hσ⟩, hV⟩ := c.property
  exact ⟨V, σ, hσ, hV⟩

def clsK (D : E.LineData X) (s : ℕ) (Λ : CLiftK (KS q s (𝒱D D)).ι D) :
    CH.H ((KS q s (𝒱D D)).ι ⋙ O (smFun X q)) 2 :=
  (CH.cx ((KS q s (𝒱D D)).ι ⋙ O (smFun X q))).cls (zK Λ s) (zK_cocycle Λ s (ks_pd q _ s))

theorem pull_cls_zK {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (h : C' ⥤ C) (s : ℕ) (hz : CH.d _ 2 (zK Λ s) = 0) (hz' : CH.d _ 2 (zK (Λ.precomp h) s) = 0) :
    (CH.Mor.restrict (g ⋙ O (smFun X q)) h).pull 2 ((CH.cx (g ⋙ O (smFun X q))).cls (zK Λ s) hz) =
      (CH.cx ((h ⋙ g) ⋙ O (smFun X q))).cls (zK (Λ.precomp h) s) hz' := by
  refine (CrystallineSemistableComparison.P.mapH_cls (CH.Mor.restrict (g ⋙ O (smFun X q)) h).hom 2 (zK Λ s) hz ?_).trans ?_
  · change CH.d _ 2 ((CH.Mor.restrict (g ⋙ O (smFun X q)) h).pullC 2 (zK Λ s)) = 0
    rw [CH.Mor.d_pullC, hz, map_zero]
  · exact cls_congr _ (zK_precomp Λ h s).symm _ _

theorem clsK_res (D : E.LineData X) {s S : ℕ} (h : s ≤ S) (Λ : CLiftK (KS q s (𝒱D D)).ι D)
    (ΛS : CLiftK (KS q S (𝒱D D)).ι D) :
    (CH.Mor.restrict ((KS q S (𝒱D D)).ι ⋙ O (smFun X q)) (ObjectProperty.ιOfLE (ks_mono q _ h))).pull 2
      (clsK q D S ΛS) = clsK q D s Λ := by
  have hz1 : CH.d _ 2 (zK (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) S) = 0 :=
    zK_cocycle (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) S
      (fun c => (ks_mono q (𝒱D D) h _ c.property).1.1)
  have hz2 : CH.d _ 2 (zK (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) s) = 0 :=
    zK_cocycle (ΛS.precomp (ObjectProperty.ιOfLE (ks_mono q (𝒱D D) h))) s (ks_pd q _ s)
  refine (pull_cls_zK q ΛS _ S _ hz1).trans ((cls_congr _ ?_ hz1 hz2).trans ?_)
  · funext σ
    exact (plogK_congr _ h (ks_pd q _ s _) (r_sub_one_mem _ σ)).symm
  · exact zK_cls_eq _ Λ s (ks_pd q _ s) hz2 _

theorem pull_restrict_comp {R : Type} [CommRing R] {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C']
    [Category.{0} C''] (F : C ⥤ ModuleCat.{0} R) (G : C' ⥤ C) (G' : C'' ⥤ C') (n : ℕ) (x : CH.H F n) :
    (CH.Mor.restrict F (G' ⋙ G)).pull n x = (CH.Mor.restrict (G ⋙ F) G').pull n ((CH.Mor.restrict F G).pull n x) :=
  (CrystallineSemistableComparison.P.pull_comp (CH.Mor.restrict F G) (CH.Mor.restrict (G ⋙ F) G') n x).1

theorem resK_res (𝒱 : Set X.Opens) {s S : ℕ} (h : s ≤ S) (x : HdR q 2) :
    resK q (KS q s 𝒱) 2 x = (CH.Mor.restrict ((KS q S 𝒱).ι ⋙ O (smFun X q)) (ObjectProperty.ιOfLE (ks_mono q 𝒱 h))).pull 2
      (resK q (KS q S 𝒱) 2 x) :=
  pull_restrict_comp (O (smFun X q)) (KS q S 𝒱).ι (ObjectProperty.ιOfLE (ks_mono q 𝒱 h)) 2 x

theorem restriction_bijective_above_dimension (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∀ S, d < S → Function.Bijective (resK q (KS q S (𝒱D D)) 2) := by
  have hP : IsProper q := isProper_of_isO1 hD
  obtain ⟨U, hU⟩ := (cov_ex q).2 d inferInstance
  have hcov : sSup (𝒱D D) = ⊤ := by
    obtain ⟨N, i, -, -, hi⟩ := hD
    exact sSup_𝒱D D N i hi
  intro S hS
  exact (k_iso q U S (fun α => by rw [hU]; exact hS) (𝒱D D) hcov 2).1

theorem test_factor (D : E.LineData X) (S : ℕ) (x : HdR q 2)
    (hA : ∀ ΛS : CLiftK (KS q S (𝒱D D)).ι D, resK q (KS q S (𝒱D D)) 2 x = clsK q D S ΛS)
    {C : Type 1} [Category.{0} C] (g' : C ⥤ (KS q S (𝒱D D)).FullSubcategory) {s : ℕ} (hsS : s ≤ S)
    (hs : ∀ c, ((g' ⋙ (KS q S (𝒱D D)).ι).obj c).pdPow s = ⊥) (Λ : CLiftK (g' ⋙ (KS q S (𝒱D D)).ι) D)
    (hz : CH.d _ 2 (zK Λ s) = 0) :
    (CH.cx ((g' ⋙ (KS q S (𝒱D D)).ι) ⋙ O (smFun X q))).cls (zK Λ s) hz =
      (CH.Mor.restrict (O (smFun X q)) (g' ⋙ (KS q S (𝒱D D)).ι)).pull 2 x := by
  let ΛS := (lift_exists q D S).some
  have hz1 : CH.d _ 2 (zK (ΛS.precomp g') S) = 0 :=
    zK_cocycle (ΛS.precomp g') S (fun c => (g'.obj c).property.1.1)
  have hz2 : CH.d _ 2 (zK (ΛS.precomp g') s) = 0 := zK_cocycle (ΛS.precomp g') s hs
  rw [pull_restrict_comp (O (smFun X q)) (KS q S (𝒱D D)).ι g' 2 x]
  change _ = (CH.Mor.restrict ((KS q S (𝒱D D)).ι ⋙ O (smFun X q)) g').pull 2 (resK q (KS q S (𝒱D D)) 2 x)
  rw [hA ΛS]
  refine (zK_cls_eq Λ (ΛS.precomp g') s hs hz hz2).trans ?_
  refine (cls_congr _ (funext fun σ => plogK_congr _ hsS (hs _) (r_sub_one_mem _ σ)) hz2 hz1).trans ?_
  exact (pull_cls_zK q ΛS g' S _ hz1).symm


theorem isFirstChernDeRham_exists_of (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∃ c : HdR q 2, IsFirstChernDeRham q D c := by
  have hk := restriction_bijective_above_dimension q d D hD
  let Λ₀ := (lift_exists q D (d + 1)).some
  let x := Function.surjInv (hk (d + 1) (by omega)).2 (clsK q D (d + 1) Λ₀)
  have hx : resK q (KS q (d + 1) (𝒱D D)) 2 x = clsK q D (d + 1) Λ₀ := Function.surjInv_eq _ _
  have hA : ∀ S, d + 1 ≤ S → ∀ ΛS : CLiftK (KS q S (𝒱D D)).ι D,
      resK q (KS q S (𝒱D D)) 2 x = clsK q D S ΛS := by
    intro S hS ΛS
    obtain ⟨x', hx'⟩ := (hk S (by omega)).2 (clsK q D S ΛS)
    have e : resK q (KS q (d + 1) (𝒱D D)) 2 x' = resK q (KS q (d + 1) (𝒱D D)) 2 x := by
      rw [resK_res q (𝒱D D) hS x', hx', clsK_res q D hS Λ₀ ΛS, hx]
    rw [← (hk (d + 1) (by omega)).1 e, hx']
  refine ⟨x, fun s C _ g hs hV Λ => ⟨zK Λ s, zK_cocycle Λ s hs, fun σ => rfl, ?_⟩⟩
  let S := max s (d + 1)
  let g' : C ⥤ (KS q S (𝒱D D)).FullSubcategory := ObjectProperty.lift _ g fun c =>
    ⟨⟨show pdP _ S = ⊥ from eq_bot_iff.2 ((dividedPowerFiltration_anti _ (le_max_left _ _)).trans (le_of_eq (hs c))),
      fun r y hy => by simpa using hy⟩, by
      obtain ⟨V, σ, hσ, hV⟩ := hV c
      exact ⟨V, ⟨σ, hσ⟩, hV⟩⟩
  exact test_factor q D S x (hA S (le_max_right _ _)) g' (le_max_left _ _) hs Λ (zK_cocycle Λ s hs)

end CrystallineSemistableComparison.Pb
end
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem isO1At_exists {R : Type} [CommRing R] {X : Scheme.{0}} (N : ℕ) (i : X ⟶ PSpace R N) :
    ∃ D : E.LineData X, IsTautologicalLineAt D N i := GlobalTheory.T.exists_twisting_line_data_projective N i

theorem isO1_exists {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (hp : IsProjOver p) :
    ∃ D : E.LineData X, IsTautologicalLine p D := by
  obtain ⟨N, i, hi, hip⟩ := hp
  obtain ⟨D, hD⟩ := isO1At_exists N i
  exact ⟨D, N, i, hi, hip, hD⟩

theorem isTwistingSheaf_pullback {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{0}} (p : X ⟶ Sp R)
    (D : E.LineData X) (hD : IsTautologicalLine p D) :
    IsTautologicalLine (pullback.snd p (spMap φ)) (D.pb (pullback.fst p (spMap φ))) := GlobalTheory.T.twisting_sheaf_base_change φ p D hD

theorem isFirstChernDeRham_exists {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) :
    ∃ c : HdR q 2, IsFirstChernDeRham q D c := isFirstChernDeRham_exists_of q d D hD


theorem isO1_etale {R : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {D : E.LineData X} (hD : IsTautologicalLine p D) :
    Etale D.f := by
  obtain ⟨N, i, -, -, h, -⟩ := hD
  exact h

theorem powK_ne_zero {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 := powK_ne_zero_main q d D hD c hc

end CrystallineSemistableComparison.Pb
end
end
