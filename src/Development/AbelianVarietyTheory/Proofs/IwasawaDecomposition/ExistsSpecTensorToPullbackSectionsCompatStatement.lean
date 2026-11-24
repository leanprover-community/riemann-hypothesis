module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpecTensorToPullbackSectionsCompat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_specTensor_to_pullback_sections_compat : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (U : X.affineOpens) (hle : ⊤ ≤ ξ ⁻¹ᵁ (U : X.Opens)) (W : Y'.affineOpens) (hW : (W : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), letI := (ρ.appLE U W hW).hom.toAlgebra; letI := (ξ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom.toAlgebra; ∃ (κ : Spec (CommRingCat.of (Γ(Y', W) ⊗[Γ(X, U)] R)) ⟶ pullback ξ ρ) (hκ : ⊤ ≤ (κ ≫ pullback.snd ξ ρ) ⁻¹ᵁ (W : Y'.Opens)), (∀ c : Γ(Y', W), (Scheme.ΓSpecIso _).hom.hom (((κ ≫ pullback.snd ξ ρ).appLE W ⊤ hκ).hom c) = c ⊗ₜ[Γ(X, U)] (1 : R)) ∧ ∀ r : R, (Scheme.ΓSpecIso _).hom.hom (κ.appTop.hom ((pullback.fst ξ ρ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = (1 : Γ(Y', W)) ⊗ₜ[Γ(X, U)] r := by
  first | exact @GlobalTheory.specTensor_to_pullback | exact GlobalTheory.specTensor_to_pullback | (intros; apply GlobalTheory.specTensor_to_pullback <;> assumption)
