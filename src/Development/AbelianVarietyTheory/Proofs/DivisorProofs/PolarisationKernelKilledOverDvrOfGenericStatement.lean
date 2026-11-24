module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationKernelKilledOverDvrOfGeneric
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.polarisation_kernel_killed_over_dvr_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) → ∀ m : ℕ, (∀ (T : Over (Sp L)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ m = 1) → ∀ (T : Over (Sp W)) (x : T ⟶ G), (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ m = 1 := by
  first | exact @GlobalTheory.KerExt.kernel_killed | exact GlobalTheory.KerExt.kernel_killed | (intros; apply GlobalTheory.KerExt.kernel_killed <;> assumption)
