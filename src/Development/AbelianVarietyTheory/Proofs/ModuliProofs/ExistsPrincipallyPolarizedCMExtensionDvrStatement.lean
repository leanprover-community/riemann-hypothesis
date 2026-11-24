module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp V)) [GrpObj A] (tK : SAB H (Sp K)) (φ : tK.G.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback tK.G A (spMap (algebraMap V K)) φ → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → ∃ (t : SAB H (Sp V)) (ν : SABMap tK t (spMap (algebraMap V K))) (e : t.G ≅ A), ν.φ ≫ e.hom.left = φ ∧ IsMonHom e.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.GoodPol.exists_sab_of_generic | exact GlobalTheory.GoodPol.exists_sab_of_generic | (intros; apply GlobalTheory.GoodPol.exists_sab_of_generic <;> assumption)
