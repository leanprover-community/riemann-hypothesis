module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexPointDerivationSeparatingParamsChar
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_complexPointDerivation_separating_params_charZero : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ∀ (x₀ : CxPts p σ) (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m (fun i => Y.presheaf.germ U.1 _ hy (f i)) → ∀ l : Fin m → ℂ, l ≠ 0 → ∃ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) ∧ (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) ∧ ∑ i, l i * δ (f i) ≠ 0 := by
  first | exact @GlobalTheory.PtDerivSep.exists_ptDer_sep | exact GlobalTheory.PtDerivSep.exists_ptDer_sep | (intros; apply GlobalTheory.PtDerivSep.exists_ptDer_sep <;> assumption)
