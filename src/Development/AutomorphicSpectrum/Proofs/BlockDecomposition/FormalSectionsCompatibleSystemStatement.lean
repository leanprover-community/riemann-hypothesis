module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalSectionsCompatibleSystem
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

theorem _root_.GlobalTheory.T.formal_sections_compatible_system : GEClosedProj → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (E : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (E e) ((E (e + 1)).pull (β e))), (∀ e, (E e).IsLB ∧ (w e).IsGen) → ∀ (m : ℕ) (z : ∀ e, Fin (m + 1) → LB.Sec (E e)), (∀ e j, SecMaps (w e) (z e j) (secPull (z (e + 1) j) (β e))) → VeryAmpleBy (Y 0).hom (E 0) (z 0) → ∃ (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (ζ : Fin (m + 1) → LB.Sec Q) (b : ∀ e, (Y e).left ⟶ X.left) (ω : ∀ e, LB.Iso (Q.pull (b e)) (E e)), Q.IsLB ∧ IsProper X.hom ∧ VeryAmpleBy X.hom Q ζ ∧ (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (ω e).IsGen) ∧ (∀ e j, SecMaps (ω e) (secPull (ζ j) (b e)) (z e j)) ∧ (∀ i₁ i₂ i₃ i₄, (∀ e (c : (E e).ι), (z e i₁).f c * (z e i₂).f c = (z e i₃).f c * (z e i₄).f c) → ∀ c : Q.ι, (ζ i₁).f c * (ζ i₂).f c = (ζ i₃).f c * (ζ i₄).f c) ∧ (∀ S : Set (Fin (m + 1)), (⨆ i ∈ S, nonzeroLocus (z 0 i) = ⊤) → ⨆ i ∈ S, nonzeroLocus (ζ i) = ⊤) := by
  exact @GlobalTheory.CompanionTheory.FormalAlg.exists_tower_algebraisation
