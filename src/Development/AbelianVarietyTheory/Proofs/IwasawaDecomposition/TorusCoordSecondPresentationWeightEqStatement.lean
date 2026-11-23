module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSecondPresentationWeightEq
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.torusCoord_secondPresentation_weight_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (e : ℕ) (xe : D'.toPre.X ≃+ D.toPre.X), GlobalTheory.CharAgree.Match (U.gt e) (U'.gt e) xe → ∀ (α' : D'.toPre.X) (jt : Fin 4 → D'.toPre.P.L.ι), LB.Coh D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt → ∀ (W' : (WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt) (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt), ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom (((U'.gt e).t α').s jt).val = ((WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) (xe α')) * ((snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs).hom (((U'.gt e).t α').s jt).val := by
  first | exact @GlobalTheory.WtSecond.wt_second | exact GlobalTheory.WtSecond.wt_second | (intros; apply GlobalTheory.WtSecond.wt_second <;> assumption)
