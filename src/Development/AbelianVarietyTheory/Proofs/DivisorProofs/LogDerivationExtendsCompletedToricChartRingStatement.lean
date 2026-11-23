module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.logDerivation_extends_completed_toricChart_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} → ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) r) = ((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) (D.1 r)) ∧ ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  first | exact @GlobalTheory.ChartDer.logDer_extend_chartRing | exact GlobalTheory.ChartDer.logDer_extend_chartRing | (intros; apply GlobalTheory.ChartDer.logDer_extend_chartRing <;> assumption)
