import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GeoRead
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FramePointBorelSectionScaling
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginComponentGenericPoint
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericLuDecompositionUnique
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AlgIndepOfSameAdjoin
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenericFlagTransitionMatrices
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.PolynomialFractionFieldDegree
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelEigenFrame
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormsContinuousAlongEmbeddingFamilies
import Development.WeilBound.CoreStatements.HodgeTatePoints.QakReindex
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ComponentKappaEquivalence
import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GenericFrameConstantAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerWeightOfZeroStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StrictWeightGrowthBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithmeticDegreePositiveHerm
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficients
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFrameComponentBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsTowerBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormTowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeightZeroSectionMembership

section
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (E₀ F : Type) [AddCommGroup E₀] [Module K E₀] [AddCommGroup F] [Module L F] (j : E₀ →+ F) (S : Type) [Finite S] (r : S → ℕ) (V : S → Submodule K E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ), GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω := K) (Ω' := L) j V b d → ∀ (e : ∀ s, Fin (r s) → E₀), (∀ s l, e s l ∈ V s) → (∀ s, LinearIndependent L fun l => j (e s l)) → ∃ v Tm : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L, (∀ s k, v s k k = 1) ∧ (∀ s l k, l < k → v s l k = 0) ∧ AlgebraicIndependent K (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin K (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) L = d ∧ (∀ s i, b s i = ∑ m, Tm s i m • ∑ l, v s l m • j (e s l)) ∧ (∀ s i m, i < m → Tm s i m = 0) ∧ ∀ s i, Tm s i i ≠ 0 := by
  first | exact @ModelDimension.generic_flag_transition_matrices | exact ModelDimension.generic_flag_transition_matrices
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_triangular_relay : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (E₀ F : Type) [AddCommGroup E₀] [Module K E₀] [AddCommGroup F] [Module L F] (j : E₀ →+ F) (S : Type) [Finite S] (r : S → ℕ) (V : S → Submodule K E₀) (b : ∀ s, Fin (r s) → F) (d : ℕ), GlobalTheory.CompanionTheory.Ar.IsGenericFlag (Ω := K) (Ω' := L) j V b d → ∀ (e : ∀ s, Fin (r s) → E₀), (∀ s l, e s l ∈ V s) → (∀ s, LinearIndependent L fun l => j (e s l)) → ∃ v Tm : ∀ s, Matrix (Fin (r s)) (Fin (r s)) L, (∀ s k, v s k k = 1) ∧ (∀ s l k, l < k → v s l k = 0) ∧ AlgebraicIndependent K (fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin K (Set.range fun q : Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) L = d ∧ (∀ s i, b s i = ∑ m, Tm s i m • ∑ l, v s l m • j (e s l)) ∧ (∀ s i m, i < m → Tm s i m = 0) ∧ ∀ s i, Tm s i i ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.generic_flag_triangular_relay
end

section
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree : ∀ (κ K L I : Type) [Field κ] [Field K] [Field L] [Algebra K L] (ψ : κ ≃+* K) (T : I → L), AlgebraicIndependent K T → ∃ φ : FractionRing (MvPolynomial I κ) →+* L, (∀ a, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.C a)) = algebraMap K L (ψ a)) ∧ (∀ i, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.X i)) = T i) ∧ (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial I κ)) L) = Module.finrank (IntermediateField.adjoin K (Set.range T)) L := by
  first | exact @ModelDimension.polynomial_fraction_field_degree | exact ModelDimension.polynomial_fraction_field_degree
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_field_extension_degree : ∀ (κ K L I : Type) [Field κ] [Field K] [Field L] [Algebra K L] (ψ : κ ≃+* K) (T : I → L), AlgebraicIndependent K T → ∃ φ : FractionRing (MvPolynomial I κ) →+* L, (∀ a, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.C a)) = algebraMap K L (ψ a)) ∧ (∀ i, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.X i)) = T i) ∧ (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial I κ)) L) = Module.finrank (IntermediateField.adjoin K (Set.range T)) L := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree
end

section
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_variables_alg_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K L : Type) [Field K] [Field L] [Algebra K L] (v : ∀ s : CMType H ⊕ CMType H, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) L), AlgebraicIndependent K (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) → ∃ T : FlagVar Dw → L, AlgebraicIndependent K T ∧ Set.range T = Set.range (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ ∀ (s : CMType H ⊕ CMType H) (i j : Fin (Dw.mult (Small.labelC s))) (hij : i < j), T ⟨Small.labelC s, ⟨(i, j), hij⟩⟩ = v s (Fin.cast (Small.mult_labelC Dw s) j) (Fin.cast (Small.mult_labelC Dw s) i) := by
  first | exact @PositivityTheory.HtPt.Qak.reindex | exact PositivityTheory.HtPt.Qak.reindex
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variables_alg_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (K L : Type) [Field K] [Field L] [Algebra K L] (v : ∀ s : CMType H ⊕ CMType H, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) L), AlgebraicIndependent K (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) → ∃ T : FlagVar Dw → L, AlgebraicIndependent K T ∧ Set.range T = Set.range (fun q : Σ s, {lk : Fin (labelRk Dw s) × Fin (labelRk Dw s) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2) ∧ ∀ (s : CMType H ⊕ CMType H) (i j : Fin (Dw.mult (Small.labelC s))) (hij : i < j), T ⟨Small.labelC s, ⟨(i, j), hij⟩⟩ = v s (Fin.cast (Small.mult_labelC Dw s) j) (Fin.cast (Small.mult_labelC Dw s) i) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.flag_variables_alg_indep
end

section
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_component_iso_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c) (ψ : kap Z ≃+* Or.𝔐.Ω₀), spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ → ∀ (y₀ : FrPt Xo c (kap Z)), y₀.x = xGen Z → letI := Small.cstAlg Or; ∀ (χ : kap Z →ₐ[c.F] RM.Ω) (y₂ : FrPt Xo c RM.Ω), χ.toRingHom = Or.𝔐.fn.comp ψ.toRingHom → FrMap χ y₀ y₂ → Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f ∧ ∀ s, ∃ e : Fin (labelRk Dw s) → Or.Fl.Li₀, (∀ k, e k ∈ Or.Fl.V₀ s) ∧ (LinearIndependent RM.Ω fun k => Or.Fl.j (e k)) ∧ ∀ k, (Or.𝔐.M.pt (Or.Fl.j (e k))).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ (Small.labelC s) (Small.labelFin Dw s k) := by
  first | exact @ModelDimension.component_kappa_equivalence | exact ModelDimension.component_kappa_equivalence
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_component_iso_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Z : Comp Xo c) (ψ : kap Z ≃+* Or.𝔐.Ω₀), spMap ψ.toRingHom ≫ genSp Z ≫ Y.j = Or.𝔐.ξ₀ → ∀ (y₀ : FrPt Xo c (kap Z)), y₀.x = xGen Z → letI := Small.cstAlg Or; ∀ (χ : kap Z →ₐ[c.F] RM.Ω) (y₂ : FrPt Xo c RM.Ω), χ.toRingHom = Or.𝔐.fn.comp ψ.toRingHom → FrMap χ y₀ y₂ → Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f ∧ ∀ s, ∃ e : Fin (labelRk Dw s) → Or.Fl.Li₀, (∀ k, e k ∈ Or.Fl.V₀ s) ∧ (LinearIndependent RM.Ω fun k => Or.Fl.j (e k)) ∧ ∀ k, (Or.𝔐.M.pt (Or.Fl.j (e k))).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ (Small.labelC s) (Small.labelFin Dw s k) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.root_origin_component_iso_relay
end

section
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_generic_frame_constants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), letI := Small.cstAlg Or; ∀ (y' : FrPt Xo c RM.Ω), Small.ptY Y y' = Or.𝔐.ξ ≫ Or.𝔐.f → ∀ (Wv : ∀ s, Fin (labelRk Dw s) → Or.𝔐.Li) (Tm : ∀ s, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) RM.Ω), (∀ s k, (Or.𝔐.M.pt (Wv s k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k)) → (∀ s i, Or.Fl.b s i = ∑ m, Tm s i m • Wv s m) → (∀ s i m, i < m → Tm s i m = 0) → (∀ s i, Tm s i i ≠ 0) → ∃ t : Ix Dw → (RM.Ω)ˣ, FrBor t y' Fr.y₀ := by
  first | exact @ModelDimension.generic_frame_constant_algebra | exact ModelDimension.generic_frame_constant_algebra
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_generic_frame_constants : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or), letI := Small.cstAlg Or; ∀ (y' : FrPt Xo c RM.Ω), Small.ptY Y y' = Or.𝔐.ξ ≫ Or.𝔐.f → ∀ (Wv : ∀ s, Fin (labelRk Dw s) → Or.𝔐.Li) (Tm : ∀ s, Matrix (Fin (labelRk Dw s)) (Fin (labelRk Dw s)) RM.Ω), (∀ s k, (Or.𝔐.M.pt (Wv s k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k)) → (∀ s i, Or.Fl.b s i = ∑ m, Tm s i m • Wv s m) → (∀ s i m, i < m → Tm s i m = 0) → (∀ s i, Tm s i i ≠ 0) → ∃ t : Ix Dw → (RM.Ω)ˣ, FrBor t y' Fr.y₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.root_origin_generic_frame_constants
end

section
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_constant_algebra_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), letI := Small.cstAlg Or; ∀ (y₂ y' : FrPt Xo c RM.Ω), Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f → y'.x = y₂.x → ∀ (s : CMType H ⊕ CMType H) (w : Fin (labelRk Dw s) → Or.𝔐.Li), (∀ k, (Or.𝔐.M.pt (w k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ (Small.labelC s) (Small.labelFin Dw s k)) → ∀ (cf : Fin (Dw.mult (Small.labelC s)) → RM.Ω) (k : Fin (labelRk Dw s)), IsCombAt y₂.x (y₂.u (Small.labelC s)) cf (y'.u (Small.labelC s) (Small.labelFin Dw s k)) → (Or.𝔐.M.pt (∑ m, cf (Small.labelFin Dw s m) • w m)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k) := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or y₂ y' h₁ hx s w hw cf k hc
  letI : Algebra (↥c.F) RM.Ω := Small.cstAlg Or
  have h : labelRk Dw s = Dw.mult (Small.labelC s) := (Small.mult_labelC Dw s).symm
  have hh : Small.labelFin Dw s = Fin.cast h := by
    funext i
    exact Fin.ext (Small.labelFin_val Dw s i)
  obtain ⟨hw', hres⟩ := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.comb_val E H Dw l Xo c _ _ Y Or.𝔐.X Or.𝔐.t
    Or.𝔐.f Or.𝔐.m RM.Ω Or.𝔐.ξ Or.𝔐.Li Or.𝔐.M y₂ h₁ (Dw.mult (Small.labelC s))
    (y₂.u (Small.labelC s)) (fun j => y₂.tan _ j) (fun j => w (Fin.cast h.symm j))
    (fun j => by rw [hw (Fin.cast h.symm j)]; rfl) cf
    (y'.u (Small.labelC s) (Small.labelFin Dw s k)) hc
  have hsum : ∑ m, cf (Small.labelFin Dw s m) • w m = ∑ j, cf j • w (Fin.cast h.symm j) := by
    rw [hh]
    exact Fintype.sum_equiv (finCongr h) _ _ (fun m => rfl)
  rw [hsum, hres]
  have hpt : Small.ptF y' = Small.ptF y₂ := by
    simp only [Small.ptF, hx]
  simp only [Small.tanY, Small.tanF, GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.tanW, hpt]
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_constant_algebra_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx), letI := Small.cstAlg Or; ∀ (y₂ y' : FrPt Xo c RM.Ω), Small.ptY Y y₂ = Or.𝔐.ξ ≫ Or.𝔐.f → y'.x = y₂.x → ∀ (s : CMType H ⊕ CMType H) (w : Fin (labelRk Dw s) → Or.𝔐.Li), (∀ k, (Or.𝔐.M.pt (w k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y₂ (Small.labelC s) (Small.labelFin Dw s k)) → ∀ (cf : Fin (Dw.mult (Small.labelC s)) → RM.Ω) (k : Fin (labelRk Dw s)), IsCombAt y₂.x (y₂.u (Small.labelC s)) cf (y'.u (Small.labelC s) (Small.labelFin Dw s k)) → (Or.𝔐.M.pt (∑ m, cf (Small.labelFin Dw s m) • w m)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.root_origin_constant_algebra_points
end

section
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory Limits
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.RdEx

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem spMap_dual_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (Formalism.L2.Pj.dualMap g) ≫ spMap (Formalism.L2.Pj.dualMap f) = spMap (Formalism.L2.Pj.dualMap (g.comp f)) := by
  rw [spMap_comp']
  congr 1
  refine RingHom.ext fun t => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

set_option maxHeartbeats 1000000 in

theorem core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (h : GenFrEx Xo c) (Z : Comp Xo c), GlobalTheory.CompanionTheory.Ar.genPt Fx.ξf = Y.j (Formalism.L2.Pj.genPt Z) → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z) → EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) → ∃ Rd : Reading Fr h Z, GeoRead Rd := by
  intro E _ _ _ H Dw l Xo c Y SS RM Sys Fx Or Fr h Z hcomp hgt hWD
  letI := Small.cstAlg Or
  obtain ⟨ψ, hψ1, hψ2⟩ := GlobalTheory.CompanionTheory.Ar.KapEquiv.exists_kap_equiv E H Dw l Xo c Y SS RM Sys Fx Or Z hcomp
  obtain ⟨hyx, y₀, hy₀, hcomb⟩ := isGenFr_genFr h Z
  let χ : kap Z →ₐ[c.F] RM.Ω := { Or.𝔐.fn.comp ψ.toRingHom with commutes' := hψ2 }
  obtain ⟨y₂, hy₂⟩ := GlobalTheory.FrameNorm.exists_frMap_along χ y₀
  obtain ⟨hpt₂, hlie⟩ := GlobalTheory.T.root_origin_component_iso_relay E H Dw l Xo c Y SS RM Sys Fx Or Z ψ hψ1 y₀ hy₀ χ y₂ rfl hy₂
  choose e he hi hev using hlie
  letI fa := Or.𝔐.fn.toAlgebra
  obtain ⟨v, Tm, hv1, hv0, hvi, hvd, hb, hT0, hTd⟩ := GlobalTheory.T.generic_flag_triangular_relay Or.𝔐.Ω₀ RM.Ω Or.Fl.Li₀ Or.𝔐.Li Or.Fl.j
    (CMType H ⊕ CMType H) (labelRk Dw) Or.Fl.V₀ Or.Fl.b Or.Fl.deg Or.Fl.generic e he hi
  obtain ⟨T, hTi, hTr, hTv⟩ := GlobalTheory.T.flag_variables_alg_indep E H Dw Or.𝔐.Ω₀ RM.Ω v hvi
  obtain ⟨φ, hφC, hφX, hφd⟩ := GlobalTheory.T.polynomial_field_extension_degree (kap Z) Or.𝔐.Ω₀ RM.Ω (FlagVar Dw) ψ T hTi
  have hφk : ∀ a : kap Z, φ (algebraMap (kap Z) (Om Z) a) = Or.𝔐.fn (ψ a) := fun a => hφC a
  have hφcst : ∀ a : c.F, φ (algebraMap c.F (Om Z) a) = Or.𝔐.cst a := fun a => by
    rw [← hψ2 a, ← hφk]
    rfl
  let φa : Om Z →ₐ[c.F] RM.Ω := { φ with commutes' := hφcst }
  obtain ⟨y', hy'⟩ := GlobalTheory.FrameNorm.exists_frMap_along φa (genFr h Z)
  have hφχ : φ.comp (algebraMap (kap Z) (Om Z)) = χ.toRingHom := RingHom.ext hφk
  have hxx : y'.x = y₂.x := by
    rw [hy'.1, hy₂.1, hyx, hy₀]
    show spMap φ ≫ spMap _ ≫ _ = spMap χ.toRingHom ≫ _
    rw [← Category.assoc, spMap_comp', hφχ]
  have hptF : Small.ptF y' = Small.ptF y₂ := pullback.hom_ext (by rw [Small.ptF_fst, Small.ptF_fst, hxx])
    (by rw [Small.ptF_snd, Small.ptF_snd])
  have hpt' : Small.ptY Y y' = Or.𝔐.ξ ≫ Or.𝔐.f := by
    rw [← hpt₂, Small.ptY, Small.ptY, hptF]
  have hcoef : ∀ (s : CMType H ⊕ CMType H) (k m : Fin (labelRk Dw s)),
      φ (genCoef Z (Small.labelC s) (Small.labelFin Dw s k) (Small.labelFin Dw s m)) = v s m k := by
    intro s k m
    unfold genCoef
    split_ifs with h1 h2
    · have := hφX ⟨Small.labelC s, ⟨(Small.labelFin Dw s k, Small.labelFin Dw s m), h1⟩⟩
      refine this.trans ((hTv s _ _ h1).trans ?_)
      rfl
    · have : k = m := Fin.ext (show (k : ℕ) = m from congrArg (fun x : Fin (Dw.mult (Small.labelC s)) => (x : ℕ)) h2)
      subst this
      rw [map_one, hv1]
    · have : m < k := by
        have h3 : ¬ (k : ℕ) < m := h1
        have h4 : (k : ℕ) ≠ m := fun e' => h2 (Fin.ext e')
        exact Fin.lt_def.2 (by omega)
      rw [map_zero, hv0 s m k this]
  have hc : ∀ (s : CMType H ⊕ CMType H) (k : Fin (labelRk Dw s)),
      IsCombAt y₂.x (y₂.u (Small.labelC s))
        (fun j => φ (genCoef Z (Small.labelC s) (Small.labelFin Dw s k) j))
        (y'.u (Small.labelC s) (Small.labelFin Dw s k)) := by
    intro s k
    have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isCombAt_bc (ψ := φ) (x0 := (genFr h Z).x) (x0' := y'.x) hy'.1
      (hcomb (Small.labelC s) (Small.labelFin Dw s k))
    have h2 : ∀ j, spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (Formalism.L2.Pj.dualMap (algebraMap (kap Z) (Om Z))) ≫
        y₀.u (Small.labelC s) j = y₂.u (Small.labelC s) j := fun j => by
      rw [hy₂.2.1, ← Category.assoc, spMap_dual_comp', hφχ]
    have h3 : y'.u (Small.labelC s) (Small.labelFin Dw s k) = spMap (Formalism.L2.Pj.dualMap φ) ≫ (genFr h Z).u (Small.labelC s) (Small.labelFin Dw s k) := hy'.2.1 _ _
    rw [h3, ← hxx]
    simpa only [h2] using h1
  let Wv : ∀ s, Fin (labelRk Dw s) → Or.𝔐.Li := fun s m => ∑ k, v s k m • Or.Fl.j (e s k)
  have hW : ∀ s k, (Or.𝔐.M.pt (Wv s k)).left ≫ Or.𝔐.m.φ = Small.tanY Y y' (Small.labelC s) (Small.labelFin Dw s k) := by
    intro s k
    have := GlobalTheory.T.root_origin_constant_algebra_points E H Dw l Xo c Y SS RM Sys Fx Or y₂ y' hpt₂ hxx s (fun m => Or.Fl.j (e s m)) (hev s) _ k (hc s k)
    simpa only [hcoef] using this
  obtain ⟨t, hbor⟩ := GlobalTheory.T.root_origin_generic_frame_constants E H Dw l Xo c Y SS RM Sys Fx Or Fr y' hpt' Wv Tm hW hb hT0 hTd
  refine ⟨⟨φ, hφcst, t, fun a f hf => ?_, ?_⟩, y', hy', hbor⟩
  · have h1 := GlobalTheory.CompanionTheory.Ar.Rec.FieldPt.evR_frBor_secZ_field E H Dw l Xo c a f RM.Ω t y' Fr.y₀ hf hbor
    obtain ⟨p, ψ₁, z, hz⟩ := hgt
    have key : ∀ {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ' : p.R →ₐ[c.F] S), FrMap ψ' z w →
        evR Xo c f w = ψ' (f p z) := by
      intro S _ _ w ψ' hw
      have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, ψ', z, hw⟩
      show evalAt _ _ f w = _
      unfold evalAt
      rw [dif_pos hft]
      exact hWD f hf.1 S _ p _ ψ' _ z w hft.choose_spec.choose_spec.choose_spec hw
    have h2 : evC h Z f = ψ₁ (f p z) := key _ _ hz
    have h3 : evR Xo c f y' = φ (evC h Z f) := by
      rw [key y' (φa.comp ψ₁) (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans ψ₁ φa hz hy'), h2]
      rfl
    show evR Xo c f Fr.y₀ = _
    rw [h1, h3]
  · have h1 := hφd
    rw [hTr, hvd] at h1
    exact h1

end GlobalTheory.CompanionTheory.Ar.Plug.RdEx

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem exists_geoRead : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp), CompOf o κ → ∀ (B : ℕ) (Z : Comp Xo c), ∃ (Fr : Small.GenFrame (o.Or B (κ Z))) (Rd : Reading Fr h Z), GeoRead Rd := by
  intro E _ _ _ H Dw l Xo c r U h e hl Y T o κ hκ B Z
  obtain ⟨Fr⟩ := GlobalTheory.CompanionTheory.Ar.GenEx.genFrame_exists E H Dw l Xo c Y (o.S B) (T.M B (κ Z)) (o.Sys (κ Z)) (o.Fx (κ Z))
    (o.Or B (κ Z))
  obtain ⟨Rd, hR⟩ := RdEx.core E H Dw l Xo c Y (o.S B) (T.M B (κ Z)) (o.Sys (κ Z)) (o.Fx (κ Z)) (o.Or B (κ Z)) Fr h Z
    (hκ Z) (hl.genT Z) hl.evalWD
  exact ⟨Fr, Rd, hR⟩

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_origin_component_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp), CompOf o κ → ∀ (B : ℕ) (Z : Comp Xo c), ∃ (Fr : Small.GenFrame (o.Or B (κ Z))) (Rd : Reading Fr h Z), GeoRead Rd := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Plug.exists_geoRead
end

section
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count

open MvPolynomial GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem cauchy_bound {D : ℕ} (L : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j) {a b : ℝ} (hb : 0 ≤ b)
    (h : a ^ D ≤ ∑ j ∈ Finset.range D, L j * a ^ j * b ^ (D - j)) :
    a ≤ (1 + ∑ j ∈ Finset.range D, L j) * b := by
  by_contra hlt
  rw [not_le] at hlt
  set S := ∑ j ∈ Finset.range D, L j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hL j
  have hB : 1 ≤ 1 + S := by linarith
  have hB0 : 0 < 1 + S := by linarith
  have ha0 : 0 < a := lt_of_le_of_lt (mul_nonneg hB0.le hb) hlt
  have hba : b ≤ a / (1 + S) := by rw [le_div_iff₀ hB0]; linarith
  have hterm : ∀ j ∈ Finset.range D, L j * a ^ j * b ^ (D - j) ≤ L j * (a ^ D / (1 + S)) := by
    intro j hj
    have hj' : j < D := Finset.mem_range.mp hj
    obtain ⟨m, hm⟩ : ∃ m, D - j = m + 1 := ⟨D - j - 1, by omega⟩
    have h1 : b ^ (D - j) ≤ a ^ (D - j) / (1 + S) := by
      rw [hm]
      calc b ^ (m + 1) ≤ (a / (1 + S)) ^ (m + 1) := pow_le_pow_left₀ hb hba _
        _ = a ^ (m + 1) / (1 + S) ^ (m + 1) := div_pow _ _ _
        _ ≤ a ^ (m + 1) / (1 + S) := by
            apply div_le_div_of_nonneg_left (by positivity) hB0
            calc 1 + S = (1 + S) ^ 1 := (pow_one _).symm
              _ ≤ (1 + S) ^ (m + 1) := pow_le_pow_right₀ hB (by omega)
    have h2 : a ^ j * a ^ (D - j) = a ^ D := by rw [← pow_add]; congr 1; omega
    calc L j * a ^ j * b ^ (D - j) ≤ L j * a ^ j * (a ^ (D - j) / (1 + S)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (hL j) (by positivity))
      _ = L j * (a ^ j * a ^ (D - j) / (1 + S)) := by ring
      _ = _ := by rw [h2]
  have hsum : a ^ D ≤ S * (a ^ D / (1 + S)) := by
    refine h.trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [hS, Finset.sum_mul]
  have hpos : 0 < a ^ D := by positivity
  have : S * (a ^ D / (1 + S)) < a ^ D := by
    rw [mul_div_assoc', div_lt_iff₀ hB0]
    nlinarith
  linarith

theorem exists_integral_bound (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (d : K → ℕ) (G F : MRing ι) (z : (Σ k, ι k) → ℂ),
      IsMultiHomog G d → IsMultiHomog F d → aeval y G = x * aeval y F → z ∈ mcPts (mCoordIdeal y) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ‖eval z (map (Int.castRingHom ℂ) G)‖ ≤ B * ‖eval z (map (Int.castRingHom ℂ) F)‖ := by
  classical
  obtain ⟨p, pm, hp⟩ := hx
  set D := p.natDegree with hD
  have hform : ∀ j : ℕ, ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧
      aeval y e = ((p.coeff j : chartRingZ y c) : Ω) * ∏ k, y ⟨k, c k⟩ ^ δ k := fun j =>
    exists_form_of_mem_chartRingZ y c hc (p.coeff j).2
  choose δ e he hev using hform
  set Δ : K → ℕ := ∑ j ∈ Finset.range D, δ j with hΔ
  have hle : ∀ j ∈ Finset.range D, ∀ k, δ j k ≤ Δ k := by
    intro j hj k
    rw [hΔ, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun j => δ j k) (fun _ _ => Nat.zero_le _) hj
  let Fm : ℕ → MRing ι := fun j => e j * chartMon c (Δ - δ j)
  have hFm : ∀ j ∈ Finset.range D, IsMultiHomog (Fm j) Δ := fun j hj =>
    homog_congr (homog_mul (he j) (homog_chartMon c (Δ - δ j))) fun k => by
      simp only [Pi.add_apply, Pi.sub_apply]
      have := hle j hj k
      omega
  have hFmv : ∀ j ∈ Finset.range D, aeval y (Fm j) =
      ((p.coeff j : chartRingZ y c) : Ω) * ∏ k, y ⟨k, c k⟩ ^ Δ k := by
    intro j hj
    simp only [Fm, map_mul, aeval_chartMon, hev]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    congr 1
    simp only [Pi.sub_apply]
    have := hle j hj k
    omega
  refine ⟨1 + ∑ j ∈ Finset.range D, coeffNorm (Fm j),
    add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => coeffNorm_nonneg _), ?_⟩
  intro d G F z hG hF hGF hz hmax hz0
  have heq : x ^ D + ∑ j ∈ Finset.range D, ((p.coeff j : chartRingZ y c) : Ω) * x ^ j = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, ← hD] at hp
    have h1 : p.coeff D = 1 := pm.coeff_natDegree
    rw [h1, map_one, one_mul] at hp
    rw [add_comm]
    exact hp
  let Q : MRing ι := chartMon c Δ * G ^ D + ∑ j ∈ Finset.range D, Fm j * G ^ j * F ^ (D - j)
  have hQ : IsMultiHomog Q (Δ + D • d) := by
    refine homog_add (homog_mul (homog_chartMon c Δ) (homog_pow hG D)) (homog_sum _ fun j hj => ?_)
    refine homog_congr (homog_mul (homog_mul (hFm j hj) (homog_pow hG j)) (homog_pow hF (D - j))) fun k => ?_
    have hj' : j ≤ D := (Finset.mem_range.mp hj).le
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : j * d k + (D - j) * d k = D * d k := by rw [← add_mul]; congr 1; omega
    omega
  have hQy : aeval y Q = 0 := by
    simp only [Q, map_add, map_mul, map_pow, map_sum, aeval_chartMon, hGF]
    have : ∀ j ∈ Finset.range D, aeval y (Fm j) * (x * aeval y F) ^ j * aeval y F ^ (D - j) =
        (∏ k, y ⟨k, c k⟩ ^ Δ k) * aeval y F ^ D * (((p.coeff j : chartRingZ y c) : Ω) * x ^ j) := by
      intro j hj
      rw [hFmv j hj, mul_pow]
      have : aeval y F ^ D = aeval y F ^ j * aeval y F ^ (D - j) := by
        rw [← pow_add]; congr 1; have := Finset.mem_range.mp hj; omega
      rw [this]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, mul_pow]
    calc _ = (∏ k, y ⟨k, c k⟩ ^ Δ k) * aeval y F ^ D *
          (x ^ D + ∑ j ∈ Finset.range D, ((p.coeff j : chartRingZ y c) : Ω) * x ^ j) := by ring
      _ = 0 := by rw [heq, mul_zero]
  have hQz := vanish hz hQ hQy
  simp only [Q, map_add, map_mul, map_pow, map_sum, eval_chartMon] at hQz
  set gz := eval z (map (Int.castRingHom ℂ) G) with hgz
  set fz := eval z (map (Int.castRingHom ℂ) F) with hfz
  set Pz := ∏ k, ‖z ⟨k, c k⟩‖ ^ Δ k with hPz
  have hPpos : 0 < Pz := Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hmain : Pz * ‖gz‖ ^ D ≤ Pz * ∑ j ∈ Finset.range D, coeffNorm (Fm j) * ‖gz‖ ^ j * ‖fz‖ ^ (D - j) := by
    have e1 : (∏ k, z ⟨k, c k⟩ ^ Δ k) * gz ^ D =
        -∑ j ∈ Finset.range D, eval z (map (Int.castRingHom ℂ) (Fm j)) * gz ^ j * fz ^ (D - j) :=
      eq_neg_of_add_eq_zero_left hQz
    have e2 : Pz * ‖gz‖ ^ D = ‖(∏ k, z ⟨k, c k⟩ ^ Δ k) * gz ^ D‖ := by
      rw [norm_mul, norm_prod, norm_pow]
      simp only [norm_pow, hPz]
    rw [e2, e1, norm_neg, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    have := norm_eval_le hmax (hFm j hj)
    calc _ ≤ (coeffNorm (Fm j) * Pz) * ‖gz‖ ^ j * ‖fz‖ ^ (D - j) := by gcongr
      _ = _ := by ring
  have h2 := le_of_mul_le_mul_left hmain hPpos
  exact cauchy_bound (fun j => coeffNorm (Fm j)) (fun _ => coeffNorm_nonneg _) (norm_nonneg _) h2

theorem exists_upper_nm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLatNm y a n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
      IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * a k) →
      aeval y g = s * aeval y h → z ∈ mcPts (mCoordIdeal y) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
        B * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k) := by
  obtain ⟨B, hB0, hB⟩ := exists_integral_bound y c hc (hs c hc)
  refine ⟨B, hB0, ?_⟩
  intro dg dh g h z hg hh hd hgy hz hmax hz0
  let up : K → ℕ := fun k => ((n : ℤ) * a k).toNat
  let dn : K → ℕ := fun k => (-((n : ℤ) * a k)).toNat
  have hud : ∀ k, (up k : ℤ) - dn k = (n : ℤ) * a k := fun k => by
    simp only [up, dn]; omega
  have hdeg : ∀ k, (dg + dn) k = (dh + up) k := fun k => by
    have h1 := hd k
    have h2 := hud k
    simp only [Pi.add_apply]
    omega
  have hG : IsMultiHomog (g * chartMon c dn) (dh + up) :=
    homog_congr (homog_mul hg (homog_chartMon c dn)) hdeg
  have hF : IsMultiHomog (h * chartMon c up) (dh + up) := homog_mul hh (homog_chartMon c up)
  have hval : aeval y (g * chartMon c dn) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * aeval y (h * chartMon c up) := by
    simp only [map_mul, aeval_chartMon, hgy]
    have : (∏ k, y ⟨k, c k⟩ ^ dn k) = (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ up k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
      congr 1
      have := hud k
      omega
    rw [this]
    ring
  have h1 := hB _ _ _ z hG hF hval hz hmax hz0
  simp only [map_mul, eval_chartMon, norm_mul, norm_prod, norm_pow] at h1
  have hr : ∀ k, ‖z ⟨k, c k⟩‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hz0 k)
  have hDn : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ dn k := Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hUp : ∏ k, ‖z ⟨k, c k⟩‖ ^ up k = (∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k)) * ∏ k, ‖z ⟨k, c k⟩‖ ^ dn k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hr k)]
    congr 1
    have := hud k
    omega
  rw [hUp] at h1
  refine le_of_mul_le_mul_right ?_ hDn
  calc _ ≤ _ := h1
    _ = _ := by ring

noncomputable def invLine (A : HermLine ι) : HermLine ι where
  a := fun k => - A.a k
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_neg]

theorem exists_lower_max (A : HermLine ι) (hA : IsSmoothHerm A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  have hI : IsSmoothHerm (invLine A) := by
    unfold IsSmoothHerm at hA ⊢
    exact hA.inv fun z hz => (A.pos z hz).ne'
  obtain ⟨C, hC1, hC⟩ := MetricMaxComparison.proof K ι (invLine A) hI
  refine ⟨C, by linarith, fun z c hz hmax => ?_⟩
  have h1 := hC z hz
  have hn : ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ = ‖z ⟨k, c k⟩‖ := fun k =>
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hmax k i)
      (norm_le_pi_norm (fun i : ι k => z ⟨k, i⟩) (c k))
  have hz0 : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi) (hmax k i)
  have h2 : (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) (invLine A).a).h z =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ := by
    show ∏ k, ‖fun i : ι k => z ⟨k, i⟩‖ ^ (- A.a k) = _
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hn k, zpow_neg]
  rw [h2] at h1
  have hP : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (hz0 k) _
  have hh : 0 < A.h z := A.pos z hz
  have h3 : (A.h z)⁻¹ ≤ C * (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ := h1
  rw [inv_le_iff_one_le_mul₀ hh] at h3
  have h4 := mul_le_mul_of_nonneg_right h3 hP.le
  rw [one_mul] at h4
  calc _ ≤ _ := h4
    _ = C * A.h z * ((∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) := by ring
    _ = C * A.h z := by rw [inv_mul_cancel₀ hP.ne', mul_one]

theorem bounded_section_smooth_metric (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (s : Ω) (hA : IsSmoothHerm A)
    (hs : s ∈ chartLatNm y A.a τ) :
    ∃ C : ℝ, 0 < C ∧ IsBoundedH (mCoordIdeal y) y A τ C s := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_lower_max A hA
  choose B hB0 hB using fun c hc => exists_upper_nm y A.a τ hs c hc
  refine ⟨1 + (∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0), ?_, ?_⟩
  · refine add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun c' _ => ?_)
    split_ifs with hc'
    · exact mul_nonneg (hB0 c' hc') (pow_nonneg hM0 τ)
    · exact le_rfl
  intro dg dh g h z hg hh hdeg hgy hz
  have hmax : ∀ k, ∃ i, ∀ i', ‖z ⟨k, i'⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz.1 k
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i0, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  choose c hcmax using hmax
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have := hcmax k i0
    rw [h0, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hz0 k (by
    have := vanish hz (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)
  have h1 := hB c hyc dg dh g h z hg hh hdeg hgy hz hcmax hz0
  have h2 := hM z c hz.1 hcmax
  have hpow : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) ^ τ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]
  have h3 : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) ≤ M ^ τ * A.h z ^ τ := by
    rw [hpow, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _) h2 τ
  have hCge : B c hyc * M ^ τ ≤
      ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0 := by
    have := Finset.single_le_sum (f := fun c : (∀ k, ι k) =>
        if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0)
      (fun c' _ => by
        split_ifs with hc'
        · exact mul_nonneg (hB0 c' hc') (pow_nonneg hM0 τ)
        · exact le_rfl) (Finset.mem_univ c)
    simpa only [dif_pos hyc] using this
  have hAh : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) := h1
    _ ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * (M ^ τ * A.h z ^ τ) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (hB0 c hyc) (norm_nonneg _))
    _ = (B c hyc * M ^ τ) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by ring
    _ ≤ (1 + ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0) *
          ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
        have : B c hyc * M ^ τ ≤ 1 + ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0 := by
          linarith
        gcongr

end GlobalTheory.CompanionTheory.Ar.Plug.Count

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count

theorem cmType_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    Nonempty (CMType H) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, h0]; simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : (τ (H.rt : E)).re = 0 := by
    have a := congrArg Complex.re h1
    have b := congrArg Complex.im h1
    simp [sq] at a b
    by_contra hne
    have : (τ (H.rt : E)).im = 0 := by
      have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at a
    nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact ⟨⟨τ, h⟩⟩
  · refine ⟨⟨(starRingEnd ℂ).comp τ, ?_⟩⟩
    have : H.rt0 = -τ (H.rt : E) := by rw [h, neg_neg]
    rw [this]
    apply Complex.ext <;> simp [hre]

end GlobalTheory.CompanionTheory.Ar.Plug.Count

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count

open MvPolynomial in

theorem charZero_of_arith {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {d : ℕ} (h : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  have hz : ∀ n : ℤ, (n : Ω) = 0 → n = 0 := by
    intro n hn
    have h1 : (C n : MRing ι) ∈ mCoordIdeal y := by
      show C n ∈ RingHom.ker (mConeMap y)
      rw [RingHom.mem_ker]
      rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, ← map_intCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    have h2 : n ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := h1
    rw [h.2.2.1] at h2
    simpa using h2
  refine ⟨fun a b hab => ?_⟩
  have := hz ((a : ℤ) - b) (by push_cast; rw [hab, sub_self])
  omega

theorem small_shift {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ q : ℕ} {s : Ω} {c : ℝ} (hτ : 0 < τ) (hq : 0 < q) (hc : 0 < c)
    (h : GroundTheory.Heights₂.Heights.HilbertSamuel.IsBoundedH (mCoordIdeal y) y A τ c s) :
    ∃ t : ℝ, IsSmallH (mCoordIdeal y) y (Small.shiftH A (q * t)) τ s := by
  refine ⟨Real.log c / (τ * q), ?_⟩
  intro dg dh g h' z hg hh hdeg he hz
  have h0 := h dg dh g h' z hg hh hdeg he hz
  have hτ' : (τ : ℝ) ≠ 0 := by positivity
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have e1 : (Small.shiftH A ((q : ℝ) * (Real.log c / (τ * q)))).h z ^ τ = c * A.h z ^ τ := by
    show (Real.exp ((q : ℝ) * (Real.log c / (τ * q))) * A.h z) ^ τ = _
    rw [mul_pow, ← Real.exp_nat_mul]
    have : (τ : ℝ) * ((q : ℝ) * (Real.log c / (τ * q))) = Real.log c := by field_simp
    rw [this, Real.exp_log hc]
  rw [e1]
  calc _ ≤ _ := h0
    _ = _ := by ring

theorem indep_mul {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ} (v : Fin r → Ω) (hv : LinearIndependent ℚ v)
    {t : Ω} (ht : t ≠ 0) : LinearIndependent ℤ (fun i => v i * t) := by
  have h1 : LinearIndependent ℤ v :=
    hv.restrict_scalars (fun a b h => by simpa using h)
  exact h1.map' (LinearMap.mulRight ℤ t) (LinearMap.ker_eq_bot.mpr (mul_left_injective₀ ht))

end GlobalTheory.CompanionTheory.Ar.Plug.Count

open GlobalTheory.CompanionTheory.Ar.Plug.Count in

theorem GlobalTheory.CompanionTheory.Ar.Plug.many_sections : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ (n : ℕ) (f : Fin n → (T.M B b).Ω), LinearIndependent ℤ f ∧ (∀ i, ∃ R, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) ∧ ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (τ : ℝ) ^ (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≤ ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * n := by
  intro hRR hG E _ _ _ H Dw l Xo c Y _ T o B b II u g hII hT1 hW hB ε hε
  have hanti : ∀ τ, StrictAnti (u τ) := fun τ a b' hab => by
    have := hW.2.1 τ a b' hab
    simpa [reW] using this
  obtain ⟨C, s, q, m, θ, hC, hs, hs0, hq, hm, hsm⟩ := GlobalTheory.T.strict_weight_growth_bound hG E H Dw l Xo c Y T o B b u hanti
  obtain ⟨hnef, hdeg, -, hpos⟩ := GlobalTheory.T.weight_threshold_limit_coefficients (CMType H) (Dw.p + Dw.q) T II B (reW u) g b s q m hII hT1 hW hB hs hs0
    (fun n => (hq n).1) hm
  have hD : 1 ≤ Top.dimFl (CMType H) (Dw.p + Dw.q) := by
    have h1 := T.j_pos
    have h2 := T.j_lt
    have hN : 2 ≤ Dw.p + Dw.q := by omega
    have h3 : 2 ≤ (Dw.p + Dw.q) * (Dw.p + Dw.q - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ _ := Nat.mul_le_mul hN (by omega)
    unfold Top.dimFl
    exact Nat.succ_le_of_lt (Nat.mul_pos (Fintype.card_pos_iff.mpr (cmType_nonempty H))
      (Nat.div_pos h3 two_pos))
  have hev := hdeg.eventually (lt_mem_nhds (show (T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε / 2 < _ by linarith))
  obtain ⟨n, hn1, hn2⟩ := (hnef.and hev).exists
  obtain ⟨P0, hP0, hsp⟩ := hn1.semipos
  have harith := (T.M B b).arith
  haveI : CharZero (T.M B b).Ω := charZero_of_arith (T.M B b).y harith
  obtain ⟨hfd, hlim⟩ := GlobalTheory.T.section_count_tendsto_geomDeg hRR hG II hII (T.M B b).K (T.M B b).ι (T.M B b).Ω (T.M B b).y
    (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)) hD harith
    (T.M B b).birational hsp.1
    (fun W _ hW' => GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.geomDeg_one_nonneg hP0 hsp hW')
  have hqn : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast (hq n).1
  have hqpos : (0 : ℝ) < (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := pow_pos hqn _
  rw [lt_div_iff₀ hqpos] at hn2
  have hlt : ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) <
      geomDeg (mCoordIdeal (T.M B b).y) (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n))
        (Top.dimFl (CMType H) (Dw.p + Dw.q)) := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) hqpos.le) hn2
  have hev2 := hlim.eventually (lt_mem_nhds hlt)
  rw [frequently_atTop]
  intro a
  obtain ⟨τ, hτ1, hτ2⟩ := (hev2.and (eventually_ge_atTop (a + 1))).exists
  have hτ0 : 0 < τ := by omega
  refine ⟨τ * q n, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_right τ (hq n).1
    omega
  haveI := hfd τ
  obtain ⟨v, hvS, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (chartLatNm (T.M B b).y (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)).a τ : Set (T.M B b).Ω)
  refine ⟨_, fun i => v i * θ n ^ τ, indep_mul v hli (pow_ne_zero _ (hq n).2.2), fun i => ?_, ?_⟩
  · obtain ⟨C', hC', hb⟩ := bounded_section_smooth_metric (T.M B b).y _ τ (v i) hsp.1 (hvS i)
    obtain ⟨t, ht⟩ := small_shift hτ0 (hq n).1 hC' hb
    exact ⟨_, hsm n τ t (v i) (hvS i) ht⟩
  · have hτr : (0 : ℝ) < (τ : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := pow_pos (by exact_mod_cast hτ0) _
    rw [lt_div_iff₀ hτr] at hτ1
    have e : (((τ * q n : ℕ) : ℝ)) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) =
        (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) * (τ : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := by
      push_cast
      rw [mul_pow, mul_comm]
    rw [e, ← mul_assoc]
    exact hτ1.le
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_intersection_height_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ (n : ℕ) (f : Fin n → (T.M B b).Ω), LinearIndependent ℤ f ∧ (∀ i, ∃ R, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) ∧ ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (τ : ℝ) ^ (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≤ ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * n := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Plug.many_sections
end

section
section
noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug

attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug.SmallProd

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Small

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem homog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hf m1 hm1 k, hg m2 hm2 k]

theorem homog_one : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
  classical
  intro m hm k
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem homog_X [DecidableEq K] (k₀ : K) (i₀ : ι k₀) :
    IsMultiHomog (MvPolynomial.X ⟨k₀, i₀⟩ : MRing ι) (Pi.single k₀ 1) := by
  classical
  intro m hm k
  have hm' : m = Finsupp.single ⟨k₀, i₀⟩ 1 := by
    rw [MvPolynomial.X, MvPolynomial.support_monomial, if_neg one_ne_zero] at hm
    exact Finset.mem_singleton.mp hm
  subst hm'
  simp only [Finsupp.single_apply, Sigma.mk.inj_iff, Pi.single_apply]
  by_cases hk : k = k₀
  · subst hk
    simp
  · simp [Ne.symm hk, hk]

def mon (c : ∀ k, ι k) (m : K → ℕ) : MRing ι := ∏ k, MvPolynomial.X ⟨k, c k⟩ ^ m k

theorem homog_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (e : ℕ) :
    IsMultiHomog (f ^ e) (e • a) := by
  induction e with
  | zero =>
    have h0 : ((0 : ℕ) • a : K → ℕ) = 0 := by
      ext k
      simp
    rw [pow_zero, h0]
    exact homog_one
  | succ n ih =>
    have h1 : ((n + 1) • a : K → ℕ) = n • a + a := by
      ext k
      simp [add_mul]
    rw [pow_succ, h1]
    exact homog_mul ih hf

theorem homog_mon (c : ∀ k, ι k) (m : K → ℕ) : IsMultiHomog (mon c m) m := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (MvPolynomial.X ⟨k, c k⟩ : MRing ι) ^ m k)
      (∑ k ∈ s, m k • Pi.single k 1) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty]
      exact homog_one
    · intro j s hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      exact homog_mul (homog_pow (homog_X j (c j)) (m j)) ih
  have hsum : (∑ k, m k • Pi.single k 1 : K → ℕ) = m := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h := key Finset.univ
  rw [hsum] at h
  exact h

private theorem mConeMap_monomial' (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (r : ℤ) :
    mConeMap y (MvPolynomial.monomial m r) =
      MvPolynomial.C (aeval y (MvPolynomial.monomial m r : MRing ι)) *
        ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ (∑ i, m ⟨k, i⟩) := by
  classical
  have hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) =
      ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ (∑ i, m ⟨k, i⟩) := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [← hX, mConeMap, MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Finsupp.prod_fintype,
    Finsupp.prod_fintype]
  · simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
    ring
  all_goals simp

theorem cone_form (y : (Σ k, ι k) → Ω) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap y h = MvPolynomial.C (aeval y h) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  have key : ∀ m ∈ MvPolynomial.support h, mConeMap y (MvPolynomial.monomial m (MvPolynomial.coeff m h)) =
      MvPolynomial.C (aeval y (MvPolynomial.monomial m (MvPolynomial.coeff m h) : MRing ι)) *
        ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
    intro m hm
    rw [mConeMap_monomial']
    simp only [hh m hm]
  conv_lhs => rw [MvPolynomial.as_sum h]
  conv_rhs => rw [MvPolynomial.as_sum h]
  simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl key

theorem sub_mem_coord (y : (Σ k, ι k) → Ω) {f g : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (hg : IsMultiHomog g d) (e : aeval y f = aeval y g) : f - g ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, map_sub, cone_form y hf, cone_form y hg, e, sub_self]

theorem aeval_eq_zero (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (hm : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  rw [mCoordIdeal, RingHom.mem_ker, cone_form y hf] at hm
  have hM : (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k))
  exact MvPolynomial.C_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hM)

theorem aeval_eq_eval (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    aeval z f = MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) := by
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def, algebraMap_int_eq]

theorem val_unique {y : (Σ k, ι k) → Ω} {a : K → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {w w' : ℂ} (h1 : HasVal y a s z w) (h2 : HasVal y a s z w') :
    w = w' := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzg⟩ := h1
  obtain ⟨dg', dh', g', h', hg', hh', hd', hy', hz0', hzg'⟩ := h2
  have hdeg : dg + dh' = dg' + dh := by
    funext k
    have e1 := hd k
    have e2 := hd' k
    simp only [Pi.add_apply]
    omega
  have hmem : g * h' - g' * h ∈ mCoordIdeal y := by
    refine sub_mem_coord y (homog_mul hg hh') ?_ ?_
    · rw [hdeg]
      exact homog_mul hg' hh
    · rw [map_mul, map_mul, hy, hy']
      ring
  have h0 := hz.2 _ hmem
  rw [← aeval_eq_eval, map_sub, map_mul, map_mul, hzg, hzg'] at h0
  have hne : aeval z h * aeval z h' ≠ 0 := mul_ne_zero hz0 hz0'
  apply mul_right_cancel₀ hne
  linear_combination h0

theorem val_mul {y : (Σ k, ι k) → Ω} {a b : K → ℤ} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (h1 : HasVal y a s z v) (h2 : HasVal y b t z w) : HasVal y (a + b) (s * t) z (v * w) := by
  obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz0, hzg⟩ := h1
  obtain ⟨dg', dh', g', h', hg', hh', hd', hy', hz0', hzg'⟩ := h2
  refine ⟨dg + dg', dh + dh', g * g', h * h', homog_mul hg hg', homog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · intro k
    simp only [Pi.add_apply, Nat.cast_add]
    linarith [hd k, hd' k]
  · rw [map_mul, map_mul, hy, hy']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz0 hz0'
  · rw [map_mul, map_mul, hzg, hzg']
    ring

theorem exists_rep (y : (Σ k, ι k) → Ω) (hb : Birational y) (hr : IsRelevant (mCoordIdeal y)) (a : K → ℤ)
    (s : Ω) : ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) = dh k + a k) ∧ aeval y g = s * aeval y h ∧ aeval y h ≠ 0 := by
  classical
  have hc : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hr k
    refine ⟨i, fun h0 => hi ?_⟩
    simp only [mCoordIdeal, RingHom.mem_ker, mConeMap, MvPolynomial.aeval_X, h0, map_zero, zero_mul]
  choose c hc using hc
  have hmon : ∀ m : K → ℕ, aeval y (mon c m) ≠ 0 := by
    intro m
    simp only [mon, map_prod, map_pow, MvPolynomial.aeval_X]
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hc k))
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ :=
    hb (s * aeval y (mon c (fun k => (-a k).toNat)) / aeval y (mon c (fun k => (a k).toNat)))
  refine ⟨d + fun k => (a k).toNat, d + fun k => (-a k).toNat, g * mon c (fun k => (a k).toNat),
    h * mon c (fun k => (-a k).toNat), homog_mul hg (homog_mon c _), homog_mul hh (homog_mon c _), ?_, ?_, ?_⟩
  · intro k
    have e1 := Int.toNat_sub_toNat_neg (a k)
    simp only [Pi.add_apply, Nat.cast_add]
    linarith
  · have h1 := hmon (fun k => (a k).toNat)
    rw [map_mul, map_mul, hgh, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff h1]
    ring
  · rw [map_mul]
    exact mul_ne_zero hh0 (hmon _)

theorem lat_mul {y : (Σ k, ι k) → Ω} {a b : K → ℤ} {s t : Ω} (hs : s ∈ chartLatNm y a 1)
    (ht : t ∈ chartLatNm y b 1) : s * t ∈ chartLatNm y (a + b) 1 := by
  intro c hc
  have key := mul_mem (hs c hc) (ht c hc)
  convert key using 1
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [← zpow_add₀ (hc k)]
  congr 1
  simp only [Pi.add_apply]
  ring

theorem valLe_mul (y : (Σ k, ι k) → Ω) (hb : Birational y) (hr : IsRelevant (mCoordIdeal y))
    (hp : (mCoordIdeal y).IsPrime) (a b : K → ℤ) (s t : Ω) {A B : ((Σ k, ι k) → ℂ) → ℝ} {w w' : MRing ι}
    (hw : IsFormOff (mCoordIdeal y) w) (hw' : IsFormOff (mCoordIdeal y) w')
    (hA : ∀ z ∈ mcPts (mCoordIdeal y), 0 ≤ A z)
    (hs : ∀ z ∈ mcPts (mCoordIdeal y), aeval z w ≠ 0 → ValLe y a s z (A z))
    (ht : ∀ z ∈ mcPts (mCoordIdeal y), aeval z w' ≠ 0 → ValLe y b t z (B z)) :
    ∃ W : MRing ι, IsFormOff (mCoordIdeal y) W ∧ ∀ z ∈ mcPts (mCoordIdeal y), aeval z W ≠ 0 →
      ValLe y (a + b) (s * t) z (A z * B z) := by
  obtain ⟨dg1, dh1, g1, h1, hg1, hh1, hd1, hy1, hy1'⟩ := exists_rep y hb hr a s
  obtain ⟨dg2, dh2, g2, h2, hg2, hh2, hd2, hy2, hy2'⟩ := exists_rep y hb hr b t
  obtain ⟨⟨dw, hdw⟩, hwP⟩ := hw
  obtain ⟨⟨dw', hdw'⟩, hwP'⟩ := hw'
  have hh1P : h1 ∉ mCoordIdeal y := fun hm => hy1' (aeval_eq_zero y hh1 hm)
  have hh2P : h2 ∉ mCoordIdeal y := fun hm => hy2' (aeval_eq_zero y hh2 hm)
  refine ⟨w * w' * h1 * h2, ⟨⟨dw + dw' + dh1 + dh2, homog_mul (homog_mul (homog_mul hdw hdw') hh1) hh2⟩, ?_⟩, ?_⟩
  · intro hm
    rcases hp.mem_or_mem hm with hm | hm
    · rcases hp.mem_or_mem hm with hm | hm
      · rcases hp.mem_or_mem hm with hm | hm
        · exact hwP hm
        · exact hwP' hm
      · exact hh1P hm
    · exact hh2P hm
  · intro z hz hW v hv
    simp only [map_mul] at hW
    obtain ⟨hW1, hz2⟩ := mul_ne_zero_iff.mp hW
    obtain ⟨hW2, hz1⟩ := mul_ne_zero_iff.mp hW1
    obtain ⟨hzw, hzw'⟩ := mul_ne_zero_iff.mp hW2
    have hv1 : HasVal y a s z (aeval z g1 / aeval z h1) :=
      ⟨dg1, dh1, g1, h1, hg1, hh1, hd1, hy1, hz1, (div_mul_cancel₀ _ hz1).symm⟩
    have hv2 : HasVal y b t z (aeval z g2 / aeval z h2) :=
      ⟨dg2, dh2, g2, h2, hg2, hh2, hd2, hy2, hz2, (div_mul_cancel₀ _ hz2).symm⟩
    have hvv := val_unique hz hv (val_mul hv1 hv2)
    rw [hvv, norm_mul]
    exact mul_le_mul (hs z hz hzw _ hv1) (ht z hz hzw' _ hv2) (norm_nonneg _) (hA z hz)

end Forms

section Root

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem nOf_add (u v : GlobalTheory.AllWt.Weight Dw) (j : Option (RootIx Dw)) : nOf (u + v) j = nOf u j + nOf v j := by
  cases j with
  | none => simp [nOf]
  | some r =>
    simp only [nOf]
    exact neg_add (u r.1 r.2) (v r.1 r.2)

theorem degOf_add (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (u v : GlobalTheory.AllWt.Weight Dw) :
    degOf RM (u + v) = degOf RM u + degOf RM v := by
  unfold degOf Top.combLine
  simp only [nOf_add, add_smul, Finset.sum_add_distrib]

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem modelSmall_mul (Or : RootOrigin Y S RM Fx) (u v : GlobalTheory.AllWt.Weight Dw) {R R' : ℝ} (hR : 0 ≤ R)
    {s s' : RM.Ω} (hs : s ∈ modelSmall Or u R) (hs' : s' ∈ modelSmall Or v R') :
    s * s' ∈ modelSmall Or (u + v) (R * R') := by
  obtain ⟨hs1, w, hw, hsw⟩ := hs
  obtain ⟨hs1', w', hw', hsw'⟩ := hs'
  have hprime : (mCoordIdeal RM.y).IsPrime := RM.arith.2.1.1
  have hrel : IsRelevant (mCoordIdeal RM.y) := RM.arith.2.1.2.2
  have hpos : ∀ r, ∀ z ∈ mcPts (mCoordIdeal RM.y), 0 < (Or.sing r).h z :=
    fun r z hz => (Or.sing r).pos z hz.1
  have hA : ∀ z ∈ mcPts (mCoordIdeal RM.y), 0 ≤ R * ∏ r, (Or.sing r).h z ^ nOf u (some r) :=
    fun z hz => mul_nonneg hR (Finset.prod_nonneg fun r _ => (zpow_pos (hpos r z hz) _).le)
  obtain ⟨W, hW, hWz⟩ :=
    valLe_mul RM.y RM.birational hrel hprime (degOf RM u) (degOf RM v) s s' hw hw' hA hsw hsw'
  refine ⟨?_, W, hW, fun z hz hz0 => ?_⟩
  · rw [degOf_add]
    exact lat_mul hs1 hs1'
  · have e : ∀ r, (Or.sing r).h z ^ nOf (u + v) (some r) =
        (Or.sing r).h z ^ nOf u (some r) * (Or.sing r).h z ^ nOf v (some r) := by
      intro r
      rw [nOf_add, zpow_add₀ (hpos r z hz).ne']
    have key : R * R' * ∏ r, (Or.sing r).h z ^ nOf (u + v) (some r) =
        (R * ∏ r, (Or.sing r).h z ^ nOf u (some r)) * (R' * ∏ r, (Or.sing r).h z ^ nOf v (some r)) := by
      simp only [e, Finset.prod_mul_distrib]
      ring
    rw [key, degOf_add]
    exact hWz z hz hz0

end Root

end GlobalTheory.CompanionTheory.Ar.Plug.SmallProd

namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem modelSmall_mul_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (u v : GlobalTheory.AllWt.Weight Dw) (R R' : ℝ), 0 ≤ R → 0 ≤ R' → ∀ s ∈ modelSmall (o.toTowerOrigin.Or B b) u R, ∀ s' ∈ modelSmall (o.toTowerOrigin.Or B b) v R', s * s' ∈ modelSmall (o.toTowerOrigin.Or B b) (u + v) (R * R') :=
  by
  intro E _ _ _ H Dw l Xo c Y _ T o B b u v R R' hR _ s hs s' hs'
  exact SmallProd.modelSmall_mul _ u v hR hs hs'

end GlobalTheory.CompanionTheory.Ar.Plug
end
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_small_sections_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (u v : GlobalTheory.AllWt.Weight Dw) (R R' : ℝ), 0 ≤ R → 0 ≤ R' → ∀ s ∈ modelSmall (o.toTowerOrigin.Or B b) u R, ∀ s' ∈ modelSmall (o.toTowerOrigin.Or B b) v R', s * s' ∈ modelSmall (o.toTowerOrigin.Or B b) (u + v) (R * R') := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Plug.modelSmall_mul_mem
end

section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_zero_section_membership : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ (x : ℝ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ∀ f ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw u 0), f ∈ GlobalTheory.AllWt.suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ GlobalTheory.AllWt.framesOn (U σ) Z, GlobalTheory.AllWt.homN (U σ) x (GlobalTheory.AllWt.wtOf Dw u 0) f z ≤ C) → f ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.bdd_mem_cuspOn | exact GlobalTheory.CompanionTheory.Ar.Plug.bdd_mem_cuspOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.bdd_mem_cuspOn <;> assumption)
end

section
section
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound

open scoped ENNReal

theorem card_le_of_intIndep {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] {d n : ℕ}
    (g : Fin n → Fin d → V) (hg : LinearIndependent ℤ g) :
    (n : ℕ∞) ≤ ((Module.finrank ℚ F * d : ℕ) : ℕ∞) * Cardinal.toENat (Module.rank F V) := by
  classical
  by_cases hfin : Module.Finite F V
  · letI : Module ℚ V := Module.compHom V (algebraMap ℚ F)
    haveI : IsScalarTower ℚ F V := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    haveI : Module.Finite ℚ V := Module.Finite.trans F V
    have hq : LinearIndependent ℚ g := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hg
    have hn := hq.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_pi_fintype] at hn
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hn
    rw [← Module.finrank_mul_finrank ℚ F V] at hn
    rw [← Module.finrank_eq_rank F V, Cardinal.toENat_nat]
    have : n ≤ Module.finrank ℚ F * d * Module.finrank F V := by
      calc n ≤ _ := hn
        _ = _ := by ring
    exact_mod_cast this
  · have htop : Cardinal.toENat (Module.rank F V) = ⊤ := by
      rw [Cardinal.toENat_eq_top]
      exact not_lt.1 fun h => hfin (Module.rank_lt_aleph0_iff.1 h)
    rw [htop]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : n = 0 := by
        by_contra hn
        have hn' : 0 < n := Nat.pos_of_ne_zero hn
        exact hg.ne_zero ⟨0, hn'⟩ (Subsingleton.elim _ _)
      simp [this]
    · have hF : 0 < Module.finrank ℚ F := Module.finrank_pos
      have : ((Module.finrank ℚ F * d : ℕ) : ℕ∞) ≠ 0 := by
        exact_mod_cast (Nat.mul_pos hF hd).ne'
      rw [ENat.mul_top this]
      exact le_top

theorem le_growth_of_frequently {D δ k₀ : ℕ} (hδ : 0 < δ) (a : ℝ) (rk : ℕ → ℕ∞)
    (H : ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ n : ℕ, ((δ : ℝ) * a - ε) * (τ : ℝ) ^ D ≤ (D.factorial : ℝ) * n ∧
      (n : ℕ∞) ≤ (δ : ℕ∞) * rk (τ + k₀)) :
    ENNReal.ofReal a ≤ GlobalTheory.CompHt.growth D rk := by
  by_contra hlt
  obtain ⟨c, h1, h2⟩ := exists_between (not_le.1 hlt)
  have hctop : c ≠ ⊤ := ne_top_of_lt h2
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hcc : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hctop
  have hca : c.toReal < a := (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 h2
  set c' := c.toReal with hc'
  set b := (c' + a) / 2 with hb
  have hb1 : c' < b := by rw [hb]; linarith
  have hb2 : b < a := by rw [hb]; linarith
  have hbpos : 0 < b := lt_of_le_of_lt hc0 hb1
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hε : 0 < (δ : ℝ) * (a - b) := mul_pos hδ' (by linarith)
  have hlim : Tendsto (fun τ : ℕ => ((τ : ℝ) / ((τ : ℝ) + (k₀ : ℝ))) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (k₀ : ℝ)).pow D
  have hev : ∀ᶠ τ : ℕ in atTop, c' / b < ((τ : ℝ) / ((τ : ℝ) + (k₀ : ℝ))) ^ D :=
    hlim.eventually_const_lt ((div_lt_one hbpos).2 hb1)
  have hfr := ((H _ hε).and_eventually (hev.and (eventually_gt_atTop 0)))
  have hfr' : ∃ᶠ τ' : ℕ in atTop, c ≤ (D.factorial : ℝ≥0∞) * (rk τ' : ℝ≥0∞) / (τ' : ℝ≥0∞) ^ D := by
    refine (tendsto_add_atTop_nat k₀).frequently (hfr.mono ?_)
    rintro τ ⟨⟨n, hn1, hn2⟩, hn3, hn4⟩
    have hτ : (0 : ℝ) < τ := by exact_mod_cast hn4
    have hτ' : (0 : ℝ) < (τ : ℝ) + k₀ := by positivity
    have hne0 : (((τ + k₀ : ℕ) : ℝ≥0∞)) ^ D ≠ 0 := by
      have : ((τ + k₀ : ℕ) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (by omega : τ + k₀ ≠ 0)
      exact pow_ne_zero _ this
    have hnet : (((τ + k₀ : ℕ) : ℝ≥0∞)) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet)]
    cases hr : rk (τ + k₀) with
    | top =>
      have hf : (D.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
      simp [ENNReal.mul_top hf]
    | coe m =>
      rw [hr] at hn2
      have hnm : n ≤ δ * m := by exact_mod_cast hn2
      have hnm' : (n : ℝ) ≤ δ * m := by exact_mod_cast hnm
      have e1 : ((δ : ℝ) * a - (δ : ℝ) * (a - b)) = δ * b := by ring
      rw [e1] at hn1
      have hfac : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
      have h3 : (δ : ℝ) * (b * (τ : ℝ) ^ D) ≤ δ * ((D.factorial : ℝ) * m) := by
        calc (δ : ℝ) * (b * (τ : ℝ) ^ D) = δ * b * (τ : ℝ) ^ D := by ring
          _ ≤ (D.factorial : ℝ) * n := hn1
          _ ≤ (D.factorial : ℝ) * (δ * m) := by gcongr
          _ = _ := by ring
      have h4 : b * (τ : ℝ) ^ D ≤ (D.factorial : ℝ) * m := le_of_mul_le_mul_left h3 hδ'
      have h5 : c' * ((τ : ℝ) + k₀) ^ D ≤ b * (τ : ℝ) ^ D := by
        rw [div_pow, div_lt_div_iff₀ hbpos (pow_pos hτ' D)] at hn3
        nlinarith [hn3]
      have hreal : c' * (((τ + k₀ : ℕ) : ℝ)) ^ D ≤ (D.factorial : ℝ) * m := by
        push_cast
        exact h5.trans h4
      have := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, hcc] at this
      simpa using this
  have : c ≤ GlobalTheory.CompHt.growth D rk := Filter.le_limsup_of_frequently_le hfr'
  exact absurd h1 (not_lt.2 this)

section Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem modelSmall_mono (Or : RootOrigin Y S RM Fx) (u : GlobalTheory.AllWt.Weight Dw) {R R' : ℝ} (hR : R ≤ R') :
    modelSmall Or u R ⊆ modelSmall Or u R' := by
  rintro s ⟨h1, w, hw, h2⟩
  refine ⟨h1, w, hw, fun z hz hne val hval => (h2 z hz hne val hval).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hR
    (Finset.prod_nonneg fun r _ => (zpow_pos ((Or.sing r).pos z hz.1) _).le)

variable {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def trHom (Rd : Reading Fr h Z) (v : GlobalTheory.AllWt.Weight Dw) : RM.Ω →+ Om Z where
  toFun := trOf Rd v
  map_zero' := by simp [trOf]
  map_add' s t := by simp [trOf, add_div]

theorem card_le_rank (G : Top.Given) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hL : CompLaws U h e) {x : ℝ}
    (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x)
    {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} [DecidableEq (CMType H)]
    {T : Top.RootTower (CMType H) (Dw.p + Dw.q)} (o : Top.GoodOrigin Y T) {B : ℕ} {b : T.Comp}
    {Fr : Small.GenFrame (o.toTowerOrigin.Or B b)} {Z : Comp Xo c} (Rd : Reading Fr h Z) (hGeo : GeoRead Rd)
    (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ))
    {k₀ τ : ℕ} (hτ : 0 < τ + k₀) {R₀ : ℝ} (hR₀ : 0 < R₀)
    {f : Fin (o.toTowerOrigin.Or B b).Fl.deg → (T.M B b).Ω}
    (hf : ∀ i, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (k₀ • u) R₀)
    (hinj : ∀ (v : GlobalTheory.AllWt.Weight Dw) (s : (T.M B b).Ω), (∀ i, trOf Rd v (s * f i) = 0) → s = 0)
    {n : ℕ} {f' : Fin n → (T.M B b).Ω} (hli : LinearIndependent ℤ f')
    (hsm : ∀ i, ∃ R, f' i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) :
    (n : ℕ∞) ≤ ((T.M B b).δ : ℕ∞) *
      Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z ((τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0))) := by
  classical
  have hvu : (τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0 = GlobalTheory.AllWt.wtOf Dw ((τ + k₀) • u) 0 :=
    (GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M B b) u).2.2.1 _
  rw [hvu, (o.toTowerOrigin.Or B b).δ_eq]
  set v : GlobalTheory.AllWt.Weight Dw := (τ + k₀) • u with hv
  have hvanti : ∀ t, StrictAnti (v t) := by
    intro t i j hij
    have h1 := hu t hij
    have h2 : (0 : ℤ) < ((τ + k₀ : ℕ) : ℤ) := by exact_mod_cast hτ
    simp only [hv, Pi.smul_apply, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left h1 h2
  have key : ∀ j i, ∃ g ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0), evC h Z g = trOf Rd v (f' j * f i) := by
    intro j i
    obtain ⟨R, hR⟩ := hsm j
    have hR' := modelSmall_mono (o.toTowerOrigin.Or B b) (τ • u) (le_max_left R 0) hR
    have hm : f' j * f i ∈ modelSmall (o.toTowerOrigin.Or B b) v (max R 0 * R₀) := by
      have := GlobalTheory.T.model_small_sections_mul E H Dw l Xo c Y T o B b (τ • u) (k₀ • u) (max R 0) R₀ (le_max_right _ _) hR₀.le _ hR' _ (hf i)
      rwa [← add_smul] at this
    obtain ⟨g, hg1, hg2, hg3⟩ := GlobalTheory.T.comp_laws_tower_bound G E H Dw l Xo c r U h e hL Y T o B b Fr Z Rd hGeo v _ hm.1
    refine ⟨g, ?_, hg3⟩
    refine GlobalTheory.T.weight_zero_section_membership E H Dw l Xo c r U h e hL hp hq x Z v hvanti g hg1 hg2 fun σ hσ => ⟨_, fun z hz =>
      GlobalTheory.T.uniform_norm_tower_bound G E H Dw l Xo c r U h e hL x hx Y T o B b Fr Z Rd hGeo v _ _
        (mul_nonneg (le_max_right _ _) hR₀.le) hm.2 g hg1 hg3 σ hσ z hz⟩
  choose g hg hgev using key
  let Gm : Fin n → Fin (o.toTowerOrigin.Or B b).Fl.deg → GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0) :=
    fun j i => ⟨g j i, hg j i⟩
  have hli' : LinearIndependent ℤ Gm := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    refine (Fintype.linearIndependent_iff.1 hli) a (hinj v _ fun i => ?_)
    have h1 : ∑ j, a j • g j i = 0 := by
      have := congrArg (fun w => ((w i : GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0)) : Rul Xo c)) ha
      simpa [Gm] using this
    have h2 : (∑ j, a j • f' j) * f i = ∑ j, a j • (f' j * f i) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    have h3 := congrArg (evCAlg h hL.genT Z) h1
    rw [map_zero, map_sum] at h3
    show trHom Rd v _ = 0
    rw [h2, map_sum, ← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul]
    exact congrArg (a j • ·) (hgev j i).symm
  have := card_le_of_intIndep (F := c.F) Gm hli'
  exact this

end Step

theorem vol_mul_flagDeg_le_growthOn : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  intro hRR G E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o κ II hκ hII _ hT1 Z u hu
  have hj := o.toTowerOrigin.j_eq
  have hp : 1 ≤ Dw.p := hj ▸ T.j_pos
  have hq : 1 ≤ Dw.q := by
    have := T.j_lt
    omega
  have hW := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M 0 (κ Z)) u
  have hdim : GlobalTheory.CompHt.dimFlag Dw = Top.dimFl (CMType H) (Dw.p + Dw.q) := hW.2.2.2.2.2.1
  have hWH : Top.WeightHyp T.j (reW u) 1 := by
    rw [hj]
    exact hW.2.2.2.2.2.2.2.1 hp hq hu
  have hB : Top.bigB0 (reW u) 1 < (⌈Top.bigB0 (reW u) 1⌉₊ : ℝ) + 1 :=
    (Nat.le_ceil _).trans_lt (lt_add_one _)
  obtain ⟨Fr, Rd, hGeo⟩ := GlobalTheory.T.tower_origin_component_bound E H Dw l Xo c r U h e hL Y T o.toTowerOrigin κ hκ ⌈Top.bigB0 (reW u) 1⌉₊ Z
  obtain ⟨k₀, R₀, f, -, hR₀, hf, -, hinj⟩ :=
    GlobalTheory.T.generic_frame_component_bound G E H Dw l Xo c h Y T o _ (κ Z) Fr Z Rd II u 1 hII hT1 hWH hB
  have main := le_growth_of_frequently (D := Top.dimFl (CMType H) (Dw.p + Dw.q)) (k₀ := k₀)
    (T.M ⌈Top.bigB0 (reW u) 1⌉₊ (κ Z)).δ_pos (T.vol (κ Z) * Top.flagDeg (reW u))
    (fun τ => Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z (τ • GlobalTheory.AllWt.wtOf Dw u 0)))) (fun ε hε => by
      refine ((GlobalTheory.T.full_intersection_height_bound hRR G E H Dw l Xo c Y T o _ (κ Z) II u 1 hII hT1 hWH hB ε hε).and_eventually
        (eventually_gt_atTop 0)).mono ?_
      rintro τ ⟨⟨n, f', hli, hsm, hle⟩, hτ⟩
      exact ⟨n, hle, card_le_rank G hL hx o Rd hGeo hp hq hu (by omega) hR₀ hf hinj hli hsm⟩)
  rw [GlobalTheory.CompHt.growthOn, hdim]
  exact main

end GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound

set_option maxHeartbeats 1000000 in

theorem _root_.GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) :=
  GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound.vol_mul_flagDeg_le_growthOn
end
end

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_norm_height_count : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count
end
