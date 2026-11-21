import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyKodairaSpencerIdentificationOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleLineBundleWeightGapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSmoothProjectiveVarietyProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleModuloEffectiveAwayFromPointPullAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefLineBundleBaseChangeFieldExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeIntersectionNumberSubvarietyThroughPositiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNefBigOfClassEqSmulAddSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulIntersectionLeOfNefClassOnClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerIsoFlagTangentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalSectionModificationWeightStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_smooth_projective_variety_properties : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y) (D : ℕ) [SmoothOfRelativeDimension D p], IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → GeometricallyConnected p → IsIntegral X ∧ IsLocallyNoetherian X ∧ SmoothOfRelativeDimension D q ∧ IsProjOver q ∧ Function.Surjective π := by
  first | exact @GlobalTheory.BaseChangeVariety.baseChange_props | exact GlobalTheory.BaseChangeVariety.baseChange_props | (intros; apply GlobalTheory.BaseChangeVariety.baseChange_props <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem closedPoint_specializing_in_open : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k) [LocallyOfFiniteType q] (U : X.Opens) (y : X), y ∈ U → ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x ∧ x ∈ U := by
  intro k _ X q _ U y hy
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace q
  have hne : (closure ({y} : Set X) ∩ (U : Set X)).Nonempty := ⟨y, subset_closure rfl, hy⟩
  have hlc : IsLocallyClosed (closure ({y} : Set X) ∩ (U : Set X)) :=
    ⟨U, closure {y}, U.isOpen, isClosed_closure, Set.inter_comm _ _⟩
  obtain ⟨x, ⟨hxc, hxU⟩, hx⟩ := nonempty_inter_closedPoints hne hlc
  exact ⟨x, (mem_closedPoints_iff).1 hx, specializes_iff_mem_closure.2 hxc, hxU⟩

end GlobalTheory
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k) [LocallyOfFiniteType q] (U : X.Opens) (y : X), y ∈ U → ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x ∧ x ∈ U := by
  atlas_forward_decl GlobalTheory.closedPoint_specializing_in_open
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNefLineBundle_baseChange_field_extension : GlobalTheory.Published.NefNumerics → ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → letI := algebraΓOfHom p; letI := algebraΓOfHom q; ∀ L : LB Y, IsNef k L → IsNef E (L.pull π) := by
  first | exact @GlobalTheory.NefFieldExt.isNef_baseChange | exact GlobalTheory.NefFieldExt.isNef_baseChange | (intros; apply GlobalTheory.NefFieldExt.isNef_baseChange <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (a b : ℕ), IsNef k N → IsBig k N → IsNef k N' → 0 < a → ∃ (N₀ : LB X) (h₀ : N₀.IsLB), cls N₀ h₀ = a • cls N hN + b • cls N' hN' ∧ IsNef k N₀ ∧ IsBig k N₀ := by
  first | exact @GlobalTheory.nef_big_of_cls_eq_smul_add_smul | exact GlobalTheory.nef_big_of_cls_eq_smul_add_smul | (intros; apply GlobalTheory.nef_big_of_cls_eq_smul_add_smul <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (N N' N₀ : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (h₀ : N₀.IsLB) (a b : ℕ) (Z : Closeds X) (e : ℕ), IsNef k N → IsNef k N' → cls N₀ h₀ = a • cls N hN + b • cls N' hN' → topologicalKrullDim (Z : Set X) = e → (a : ℤ) ^ e * interNumRed k Z (fun _ : Fin e => N) ≤ interNumRed k Z (fun _ : Fin e => N₀) := by
  first | exact @GlobalTheory.mixExp_interNumRed | exact GlobalTheory.mixExp_interNumRed | (intros; apply GlobalTheory.mixExp_interNumRed <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (L M M' : LB X) (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (a b : ℕ) (C : Closeds X), IsCompleteCurve k C → cls L hL = a • cls M hM + b • cls M' hM' → interNumRed k C ![L] = a * interNumRed k C ![M] + b * interNumRed k C ![M'] := by
  first | exact @GlobalTheory.interNumRed_of_cls_eq_nsmul_add | exact GlobalTheory.interNumRed_of_cls_eq_nsmul_add | (intros; apply GlobalTheory.interNumRed_of_cls_eq_nsmul_add <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective : GlobalTheory.Published.IsolatedNonKltDivisor → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q; ∀ (N₀ : LB X) (r : ℕ) (x : X), 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → IsClosed ({x} : Set X) → (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → (((D + 1).choose 2 : ℕ) : ℝ) ^ e < (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e) → ∃ (m' : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m' ∧ D₀.Eff ∧ (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = interNumRed ℂ C ![N₀] / r) ∧ x ∈ U ∧ (∀ y ∈ U, y ≠ x → KltAt q D (qWeil D₀ m') y) ∧ ¬ KltAt q D (qWeil D₀ m') x := by
  first | exact @GlobalTheory.KollarApp.isolatedNonKlt_smooth | exact GlobalTheory.KollarApp.isolatedNonKlt_smooth | (intros; apply GlobalTheory.KollarApp.isolatedNonKlt_smooth <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nadel_vanishing_canonical_add_boundary : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → letI := algebraΓOfHom q; ∀ (K : CanonLB q D) (B M₀ : LB X) (hB : B.IsLB) (D₀ : CartierDiv X) (m' r : ℕ), 0 < m' → 0 < r → D₀.Eff → IsNef ℂ M₀ → IsBig ℂ M₀ → (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![B] : ℚ) = interNumRed ℂ C ![toLB D₀] / m' + interNumRed ℂ C ![M₀] / r) → ∃ J : X.IdealSheafData, (∀ y : X, y ∈ J.support ↔ ¬ KltAt q D (qWeil D₀ m') y) ∧ ∀ i, 0 < i → Subsingleton (coh (twist (idealModule J) (tens K.bundle B)) i) := by
  first | exact @GlobalTheory.NadelApp.nadel_canonical_add | exact GlobalTheory.NadelApp.nadel_canonical_add | (intros; apply GlobalTheory.NadelApp.nadel_canonical_add <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_point : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB → ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U → (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) → ∃ s : L.Sec, x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated | exact GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated | (intros; apply GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

noncomputable section

namespace GlobalTheory.FieldDescent

open scoped TensorProduct

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC in

theorem exists_sec_of_pull {F E : Type} [Field F] [Field E] [Algebra F E] {Y X : Scheme.{0}}
    {p : Y ⟶ Sp F} {q : X ⟶ Sp E} {π : X ⟶ Y} (H : IsPullback π q p (spMap (algebraMap F E)))
    [CompactSpace Y] [Y.IsSeparated] {N : LB Y} (hN : N.IsLB) (σ : (N.pull π).Sec) (x : X)
    (hx : x ∈ nonzeroLocus σ) : ∃ θ : N.Sec, π x ∈ nonzeroLocus θ := by
  classical
  obtain ⟨n, V, c, hVa, hVc, hcov⟩ := exists_affine_chart_cover N hN
  letI instV : ∀ a, Algebra F Γ(Y, V a) := fun a => (algX p (V a)).toAlgebra
  letI instW : ∀ ab : Fin n × Fin n, Algebra F Γ(Y, V ab.1 ⊓ V ab.2) := fun ab => (algX p _).toAlgebra
  let δ : (∀ a, Γ(Y, V a)) →ₗ[F] (∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) :=
    { toFun := fun f ab => dfun N V c hVc f ab.1 ab.2
      map_add' := fun f g => by
        funext ab
        simp only [dfun, Pi.add_apply, map_add, mul_add]
        abel
      map_smul' := fun r f => by
        funext ab
        simp only [dfun, RingHom.id_apply, Pi.smul_apply, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        rw [ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, ReciprocityTheory.ChartRestriction.G.DVR.rs_mul, rs_algX, rs_algX]
        ring }
  have hδ : ∀ m, δ m = 0 ↔ dfun N V c hVc m = 0 := fun m => by
    constructor
    · intro h; funext a b; exact congrFun h (a, b)
    · intro h; funext ab; exact congrFun (congrFun h ab.1) ab.2
  have hV'c : ∀ a, π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤ ≤ (N.pull π).U (fun _ => c a) := fun a y hy =>
    Set.mem_iInter.2 fun _ => hVc a hy.1
  let m' : ∀ a, Γ(X, π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤) := fun a => ReciprocityTheory.ChartRestriction.G.DVR.rs (hV'c a) (σ.f (fun _ => c a))
  let t : (∀ a, Γ(Y, V a)) ⊗[F] E := (TensorProduct.piLeft (R := F) (N := E) (M := fun a => Γ(Y, V a))).symm
    (fun a => (eTens p q π H (V a) (hVa a)).symm (m' a))
  have hpt : ∀ a, (TensorProduct.piLeft (R := F) (N := E) (M := fun a => Γ(Y, V a))) t a =
      (eTens p q π H (V a) (hVa a)).symm (m' a) := fun a => by
    simp only [t, LinearEquiv.apply_symm_apply]
  have ht : δ.rTensor E t = 0 := by
    apply (TensorProduct.piLeft (R := F) (N := E) (M := fun ab : Fin n × Fin n => Γ(Y, V ab.1 ⊓ V ab.2))).injective
    rw [map_zero]
    funext ab
    obtain ⟨a, b⟩ := ab
    rw [piLeft_apply_eq, ← LinearMap.rTensor_comp_apply]
    have hdec : (LinearMap.proj (a, b) : (∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) →ₗ[F] _).comp δ =
        (rsL p (V a) (V a ⊓ V b) inf_le_left).comp (LinearMap.proj a) -
          (mulL p (V a ⊓ V b) (ReciprocityTheory.ChartRestriction.G.Semi.res (pair_le N V c hVc a b) (N.g (c a) (c b))).val).comp
            ((rsL p (V b) (V a ⊓ V b) inf_le_right).comp (LinearMap.proj b)) := by
      ext f; rfl
    rw [hdec, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply,
      LinearMap.rTensor_comp_apply, ← piLeft_apply_eq, ← piLeft_apply_eq, hpt, hpt]
    apply (eTens p q π H (V a ⊓ V b) ((hVa a).inf (hVa b))).injective
    rw [map_sub, eTens_rs p q π H (V a) (V a ⊓ V b) (hVa a) _ inf_le_left, eTens_mul,
      eTens_rs p q π H (V b) (V a ⊓ V b) (hVa b) _ inf_le_right, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply, Pi.zero_apply, map_zero, sub_eq_zero]
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.fn_ext fun y hy => ?_
    have hyk : y ∈ (N.pull π).U (fun _ => c a) := Set.mem_iInter.2 fun _ => hVc a hy.1.1
    have hyl : y ∈ (N.pull π).U (fun _ => c b) := Set.mem_iInter.2 fun _ => hVc b hy.1.2
    have hyk' : y ∈ π ⁻¹ᵁ V a ⊓ q ⁻¹ᵁ ⊤ := ⟨hy.1.1, hy.2⟩
    have hyl' : y ∈ π ⁻¹ᵁ V b ⊓ q ⁻¹ᵁ ⊤ := ⟨hy.1.2, hy.2⟩
    have hφy : π y ∈ V a ⊓ V b := hy.1
    simp only [m']
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_mul _ y _ hy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hy,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hyk', ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hy,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res _ y _ hyl', ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE π _ _ _ (𝟙 _) y hy]
    erw [Category.id_comp, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_unit _ y _ hφy, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_res _ y _ hφy]
    erw [gs_sec (N.pull π) σ (fun _ => c a) (fun _ => c b) y hyk hyl,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pull_g N π (𝟙 _) y (fun _ => c a) (fun _ => c b) hyk hyl, Category.id_comp]
  let b := Module.Basis.ofVectorSpace F E
  let e₁ := TensorProduct.equivFinsuppOfBasisRight (M := ∀ a, Γ(Y, V a)) b
  let e₂ := TensorProduct.equivFinsuppOfBasisRight (M := ∀ ab : Fin n × Fin n, Γ(Y, V ab.1 ⊓ V ab.2)) b
  have nat : ∀ u β, e₂ (δ.rTensor E u) β = δ (e₁ u β) := by
    intro u β
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul m a =>
      simp only [LinearMap.rTensor_tmul, e₁, e₂, TensorProduct.equivFinsuppOfBasisRight_apply_tmul,
        Finsupp.mapRange_apply, map_smul]
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  have hβ : ∀ β, dfun N V c hVc (e₁ t β) = 0 := fun β =>
    (hδ _).1 (by rw [← nat, ht, map_zero, Finsupp.zero_apply])
  choose θ hθ using fun β => exists_glue N V c hVc hN hcov (e₁ t β) (hβ β)
  by_contra hcon
  push_neg at hcon
  obtain ⟨j, hj⟩ : ∃ j, π x ∈ V j := TopologicalSpace.Opens.mem_iSup.1 (by rw [hcov]; trivial)
  have hxj : x ∈ π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤ := ⟨hj, trivial⟩
  have hxc : x ∈ (N.pull π).U (fun _ => c j) := hV'c j hxj
  have hu := (mem_nonzeroLocus_iff_isUnit σ hxc).1 hx
  rw [← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res (𝟙 X) x (hV'c j) hxj] at hu
  change IsUnit (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (m' j)) at hu
  have hexp : t = (e₁ t).sum fun β m => m ⊗ₜ[F] b β := by
    rw [← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : m' j = (e₁ t).sum fun β m => (π.appLE (V j) (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (m j) *
      algX q (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) (b β) := by
    have h1 := hpt j
    rw [hexp, piLeft_apply_eq, Finsupp.sum, map_sum] at h1
    simp only [LinearMap.rTensor_tmul, LinearMap.proj_apply] at h1
    rw [← RingEquiv.apply_symm_apply (eTens p q π H (V j) (hVa j)) (m' j), ← h1, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [eTens_tmul]
  have key : ∀ β, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _
      ((π.appLE (V j) (π ⁻¹ᵁ V j ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom (e₁ t β j)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := fun β => by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_appLE π _ _ _ (𝟙 X) x hxj, Category.id_comp, ← hθ β]
    simp only [ev]
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_res π x (hVc j) hj, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      ← mem_nonzeroLocus_iff_pull (θ β) π x (hVc j hj)]
    exact hcon (θ β)
  have hmem : ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (m' j) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    rw [hm, Finsupp.sum, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq (𝟙 X) x _ hxj, map_sum, map_sum]
    refine Ideal.sum_mem _ fun β _ => ?_
    rw [map_mul, map_mul, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq (𝟙 X) x _ hxj]
    exact Ideal.mul_mem_right _ _ (key β)
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu

theorem exists_sec_tens_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ (L M : LB Y), L.IsLB → M.IsLB → ∀ x : X, (∃ s : (tens (L.pull π) (M.pull π)).Sec, x ∈ nonzeroLocus s) → ∃ s : (tens L M).Sec, π x ∈ nonzeroLocus s := by
  intro k E _ _ _ Y X p q π H hP L M hL hM x ⟨s, hs⟩
  have : IsProper p := CommonModel.isProper_of_isProjOver hP
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  have hN := isLB_tens hL hM
  have hNp := LB.isLB_pull hN π
  have hT := isLB_tens (LB.isLB_pull hL π) (LB.isLB_pull hM π)
  have iso : LBIso ((tens L M).pull π) (tens (L.pull π) (M.pull π)) := by
    refine (cls_eq_iff hNp hT).1 ?_
    rw [cls_pull hN π hNp, cls_tens hL hM hN, map_add, cls_tens (LB.isLB_pull hL π) (LB.isLB_pull hM π) hT,
      cls_pull hL π, cls_pull hM π]
  obtain ⟨s₂, hs₂⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hNp hT iso s
  exact exists_sec_of_pull H hN s₂ x (hs₂ ▸ hs)

end GlobalTheory.FieldDescent
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (Y X : Scheme.{0}) (p : Y ⟶ Sp k) (q : X ⟶ Sp E) (π : X ⟶ Y), IsPullback π q p (spMap (algebraMap k E)) → IsProjOver p → ∀ (L M : LB Y), L.IsLB → M.IsLB → ∀ x : X, (∃ s : (tens (L.pull π) (M.pull π)).Sec, x ∈ nonzeroLocus s) → ∃ s : (tens L M).Sec, π x ∈ nonzeroLocus s := by
  atlas_forward_decl GlobalTheory.FieldDescent.exists_sec_tens_of_baseChange
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.EffGen

theorem core_gen (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ)
    [SmoothOfRelativeDimension D q] (hq : IsProjOver q) (hD : 1 ≤ D) :
    letI := algebraΓOfHom q
    ∀ (K : CanonLB q D) (N N' B : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : X),
      IsClosed ({x} : Set X) → IsNef ℂ N → IsBig ℂ N → IsNef ℂ N' → (D + 1).choose 2 < m →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed ℂ Z (fun _ : Fin e => N)) →
      cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, x ∈ nonzeroLocus s := by
  letI := algebraΓOfHom q
  intro K N N' B hN hN' hB m x hx hNn hNb hN'n hm hpos hBc
  have hm1 : 1 ≤ m := by omega
  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ := GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul hNN ℂ X q hq N N' hN hN' (2 * m - 1) 2 hNn hNb hN'n (by omega)
  obtain ⟨m', D₀, U, hm', hD₀, hcur, hxU, hklt, hnk⟩ := GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective hK.2 X q D hq hD N₀ 2 x two_pos hn₀ hb₀ hx
    (fun Z e hZ hxZ he hdim => by
      have h1 := hpos Z e hZ hxZ he hdim
      have h2 := GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed hNN ℂ X q hq N N' N₀ hN hN' h₀ (2 * m - 1) 2 Z e hNn hN'n hc₀ hdim
      have h3 : ((2 * m - 1 : ℕ) : ℤ) ^ e ≤ interNumRed ℂ Z (fun _ : Fin e => N₀) := by
        have : (0 : ℤ) ≤ ((2 * m - 1 : ℕ) : ℤ) ^ e := by positivity
        nlinarith
      have h3' : (((2 * m - 1 : ℕ) : ℝ)) ^ e ≤ (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) := by
        exact_mod_cast h3
      have h4 : ((((D + 1).choose 2 : ℕ) : ℝ) * 2) ^ e < ((2 * m - 1 : ℕ) : ℝ) ^ e := by
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        have : (D + 1).choose 2 * 2 < 2 * m - 1 := by omega
        exact_mod_cast this
      rw [lt_div_iff₀ (by positivity), ← mul_pow]
      push_cast at h4 h3' ⊢
      linarith)
  obtain ⟨J, hJ, hvan⟩ := GlobalTheory.T.nadel_vanishing_canonical_add_boundary hK.1 X q D hq K B N hB D₀ m' 2 hm' two_pos hD₀ hNn hNb
    (fun C hC => by
      have e1 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq B N N' hB hN hN' m 1 C hC (by rw [hBc, one_smul])
      have e2 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq N₀ N N' h₀ hN hN' (2 * m - 1) 2 C hC hc₀
      have e3 := hcur C hC
      rw [e3, e1, e2]
      have : ((2 * m - 1 : ℕ) : ℚ) = 2 * m - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [this]
      ring)
  exact GlobalTheory.T.exists_section_nonvanishing_point ℂ X q hq (tens K.bundle B) (isLB_tens K.isLB hB) J x U hx hxU
    (fun y hy => by
      rw [hJ]
      constructor
      · intro h
        by_contra hne
        exact h (hklt y hy hne)
      · rintro rfl
        exact hnk) (hvan 1 one_pos)

theorem effective_generation : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  intro hK hNN F _ _ Y p D _ hproj hgc hD1
  letI := algebraΓOfHom p
  intro K N N' B hN hN' hB a m y hNn hN'n hm hdec hBc
  obtain ⟨N₁, N₂, h₁, h₂, ha, hcls, hamp, hN₂⟩ := hdec
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ F
  let σ : F →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := F)).toRingHom
  letI : Algebra F ℂ := σ.toAlgebra
  let π := pullback.fst p (spMap (algebraMap F ℂ))
  let q := pullback.snd p (spMap (algebraMap F ℂ))
  have H : IsPullback π q p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hXi, hXn, hsm, hqp, hsurj⟩ := GlobalTheory.T.baseChange_smooth_projective_variety_properties F ℂ Y _ p q π D H hproj hgc
  haveI := hXi; haveI := hXn; haveI := hsm
  letI := algebraΓOfHom q
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  obtain ⟨y', rfl⟩ := hsurj y
  haveI : Smooth q := SmoothOfRelativeDimension.smooth D q
  obtain ⟨m₁, A, s₁, hm₁, hA, hAa, hy⟩ := hamp
  obtain ⟨x, hxc, hyx, hxU⟩ := GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType ℂ _ q (π ⁻¹ᵁ nonzeroLocus s₁) y' hy
  have hAx : AmpleAt (N₁.pull π) x := GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine Y _ π N₁ h₁ x ⟨m₁, A, s₁, hm₁, hA, hAa, hxU⟩
  have hNnC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N hNn
  have hN'nC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N' hN'n
  have hN₂C := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N₂ hN₂
  have hc : a • cls (N.pull π) (pull_isLB hN π) = cls (N₁.pull π) (pull_isLB h₁ π) + cls (N₂.pull π) (pull_isLB h₂ π) := by
    rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add]
  have hbig := GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hpos := GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hcB : cls (B.pull π) (pull_isLB hB π) = m • cls (N.pull π) (pull_isLB hN π) + cls (N'.pull π) (pull_isLB hN' π) := by
    rw [cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add, map_nsmul]
  obtain ⟨s, hs⟩ := core_gen hK hNN _ q D hqp hD1 (CanonLB.baseChange H K) (N.pull π) (N'.pull π) (B.pull π)
    _ _ _ m x hxc hNnC hbig hN'nC hm hpos hcB
  exact GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange F ℂ Y _ p q π H hproj K.bundle B K.isLB hB y' ⟨s, hyx.mem_open (nonzeroLocus s).isOpen hs⟩

end GlobalTheory.EffGen
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effective_generation_canonical_nef_numberField : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  atlas_forward_decl GlobalTheory.EffGen.effective_generation
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModifRefl

theorem exists_sec_canon_tens_pull_id : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ) [SmoothOfRelativeDimension D p] [SmoothOfRelativeDimension D (𝟙 Y ≫ p)] (B : LB Y), B.IsLB → ∀ (s : H0 p (tens (CanonLB.all p D).bundle B) ⊤) (y : Y), y ∈ nonzeroLocus (toSec s) → ∃ s' : H0 (𝟙 Y ≫ p) (tens (CanonLB.all (𝟙 Y ≫ p) D).bundle (B.pull (𝟙 Y))) ⊤, y ∈ nonzeroLocus (toSec s') := by
  intro k _ Y p D _ inst2 B hB s y hy
  revert inst2
  generalize hq : 𝟙 Y ≫ p = q
  simp only [Category.id_comp] at hq
  subst hq
  intro inst2
  have hK : (CanonLB.all p D).bundle.IsLB := (CanonLB.all p D).isLB
  have hBp : (B.pull (𝟙 Y)).IsLB := LB.isLB_linComb hB _ _
  have H1 : LBIso (tens (B.pull (𝟙 Y)) (CanonLB.all p D).bundle) (tens B (CanonLB.all p D).bundle) :=
    GlobalTheory.CechPic.tens_congr_left hK (DescendedPrincipal.lbIso_pull_id hB)
  have H : LBIso (tens (CanonLB.all p D).bundle (B.pull (𝟙 Y))) (tens (CanonLB.all p D).bundle B) :=
    LBIso.trans (isLB_tens hK hBp) (isLB_tens hBp hK) (isLB_tens hK hB)
      (GlobalTheory.CechPic.tens_comm_iso hK hBp)
      (LBIso.trans (isLB_tens hBp hK) (isLB_tens hB hK) (isLB_tens hK hB) H1
        (GlobalTheory.CechPic.tens_comm_iso hB hK))
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (isLB_tens hK hBp) (isLB_tens hK hB) H (toSec s)
  refine ⟨H0.ofSec p ⊤ t, ?_⟩
  have e : toSec (H0.ofSec p ⊤ t) = t := by
    unfold toSec
    exact Equiv.ofBijective_symm_apply_apply _ _ _
  rw [e, ht]
  exact hy

end GlobalTheory.ModifRefl
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HSApp

theorem gapGe_stdWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    GapGe 1 (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw) := by
  intro τ k hk
  simp only [gap, dif_pos hk, GlobalTheory.CompHt.stdWt]
  push_cast
  omega

theorem gapGe_sub_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (m : ℕ) (b : AllWt.Weight Dw) (h : GapGe (m : ℤ) b) :
    GapGe 0 (b - m • (GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) : AllWt.Weight Dw)) := by
  intro τ k hk
  have h1 := h τ k hk
  simp only [gap, dif_pos hk, Pi.sub_apply, Pi.smul_apply, GlobalTheory.CompHt.stdWt] at h1 ⊢
  rw [nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  linarith

theorem cls_common_nsmul {Y : Scheme.{0}} {Λ : Type} [AddCommGroup Λ] {B : Λ → LB Y} (C : Common B) (n : ℕ) (a : Λ) :
    cls (B (n • a)) (C.isLB (n • a)) = n • cls (B a) (C.isLB a) := by
  induction n with
  | zero =>
    have h := cls_common_add C 0 0
    simp only [add_zero] at h
    simp only [zero_nsmul]
    exact left_eq_add.1 h
  | succ n ih =>
    rw [succ_nsmul, cls_common_add C, ih, succ_nsmul]

theorem exists_canSec_ne_zero_at : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → 1 ≤ dimFlag Dw → ∀ (hV : IsVariety₀ TF.X Z) (la : AllWt.Weight Dw), GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → letI := hV.1; ∀ y ∈ U₀ TF.X Z, ∃ g : H0 (str₀ TF.X Z) (tens (CanonLB.all (str₀ TF.X Z) (dimFlag Dw)).bundle (L₀ TF.X Z (la - FlagTan.kap Dw))) ⊤, y ∈ nonzeroLocus (toSec g) := by
  intro hP hN hNa hS hT hL E _ _ _ H Dw l Xo c TF Z hF hD hV la hg
  letI := hV.1
  intro y hy
  set std : AllWt.Weight Dw := GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) with hstd_def
  set m : ℕ := (dimFlag Dw + 1).choose 2 + 1 with hm_def
  have hstd : GapGe 1 std := gapGe_stdWt Dw
  have hmu : GapGe 0 (la - FlagTan.kap Dw - m • std) := gapGe_sub_smul m _ hg
  letI := algebraΓOfHom (str₀ TF.X Z)
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → IsNef c.F (L₀ TF.X Z w) :=
    fun w hw => GlobalTheory.T.nef_line_bundle_weight_gap hP hN hL E H Dw l Xo c TF Z hF w hw
  obtain ⟨mu, hmu0, m', hm', hA⟩ := GlobalTheory.T.ample_line_bundle_weight_gap hP hN hS hT E H Dw l Xo c TF Z hF std hstd y hy
  have C := common₀ TF.X Z
  have e₁ : m' • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) =
      cls (L₀ TF.X Z (m' • std - mu)) (isLB_L₀ TF.X Z _) + cls (L₀ TF.X Z mu) (isLB_L₀ TF.X Z mu) := by
    have h := cls_common_add (common₀ TF.X Z) (m' • std - mu) mu
    rw [sub_add_cancel] at h
    rw [← h]
    exact (cls_common_nsmul (common₀ TF.X Z) m' std).symm
  have e₂ : cls (L₀ TF.X Z (la - FlagTan.kap Dw)) (isLB_L₀ TF.X Z _) =
      m • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) + cls (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (isLB_L₀ TF.X Z _) := by
    have h := cls_common_add (common₀ TF.X Z) (m • std) (la - FlagTan.kap Dw - m • std)
    rw [add_sub_cancel] at h
    rw [h]
    exact congrArg (· + _) (cls_common_nsmul (common₀ TF.X Z) m std)
  obtain ⟨s, hs⟩ := GlobalTheory.T.effective_generation_canonical_nef_numberField hNa hN c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) hV.2.1 hV.2.2 hD
    (CanonLB.all _ _) (L₀ TF.X Z std) (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (L₀ TF.X Z (la - FlagTan.kap Dw))
    (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) m' m y (nef std (hstd.mono (by norm_num))) (nef _ hmu)
    (by omega) ⟨_, _, isLB_L₀ TF.X Z (m' • std - mu), isLB_L₀ TF.X Z mu, hm', e₁, hA, nef mu hmu0⟩ e₂
  refine ⟨H0.ofSec _ ⊤ s, ?_⟩
  rwa [show toSec (H0.ofSec (str₀ TF.X Z) ⊤ s) = s from H0.bijective_ofSec_top.1 (ofSec_toSec _)]

theorem freeOnOpen_of_gapGe : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed Xo c → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  intro hP hG hQ hNa hPr hS hT hL E _ _ _ H Dw l Xo c TF Z r U hF hD la hg hC
  have hV := @GlobalTheory.VarFlag.isVariety₀_flag E _ _ _ H Dw l Xo c TF Z hF
  have hpq : 1 ≤ Dw.p + Dw.q := by
    by_contra h
    have h0 : Dw.p + Dw.q = 0 := by omega
    have : dimFlag Dw = 0 := by
      unfold GlobalTheory.FlagTan.dimFlag
      rw [h0]
      simp
    omega
  let M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw) := Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)
  obtain ⟨ω⟩ := GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z M (fun K _ _ y => GlobalTheory.T.kodaira_spencer_iso_flag_tangent hP hG E H Dw l Xo c K y hpq)
  intro y hy
  rw [mem_support_baseIdeal]
  push_neg
  obtain ⟨g, hgy⟩ := exists_canSec_ne_zero_at hP hQ.nef hNa hS hT hL E H Dw l Xo c TF Z hF hD hV la hg y hy
  haveI := hV.1
  haveI : SmoothOfRelativeDimension (dimFlag Dw) (𝟙 (Y₀ TF.X Z) ≫ str₀ TF.X Z) := M.smooth
  obtain ⟨g', hg'⟩ := GlobalTheory.ModifRefl.exists_sec_canon_tens_pull_id c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) _ (isLB_L₀ TF.X Z _) g y hgy
  have hyM : (y : M.X) ∈ M.off := by
    rw [M.off_eq]
    exact hy
  obtain ⟨s, hs, hsy⟩ := GlobalTheory.T.canonical_section_modification_weight hP hG E H Dw l Xo c TF Z hF M ω la g' y hyM hg'
  exact ⟨s, hC.2 hs, hsy⟩

end GlobalTheory.HSApp
end
end
