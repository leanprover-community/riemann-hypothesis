module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FinrankOfExpBij
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsSymmetricOfSymmetryGenerator
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PelUnifPowerDvr

theorem main : Laws → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (j : ℕ), ∃ (t' : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P' : Geo.Tor.PELUnif (maximalIdeal V) t') (pG : IsPowGrp t'.G t.G j) (pD : IsPowDeg P'.D.toPre P.D.toPre j) (pA : IsPowPolAV P'.A P.A j), Nonempty (UnifPowOf3 pD pA pG P'.U P.U) ∧ (∀ a i, t'.act.act a ≫ pG.pr i = pG.pr i ≫ t.act.act a) ∧ ∀ (a : NumberField.RingOfIntegers E) (x : P'.D.toPre.X), pD.xe (a • x) = a • pD.xe x := by
  intro hL hT V _ _ _ E _ _ _ H t P j
  obtain ⟨A', pA, -⟩ := GlobalTheory.exists_powPolAV _ P.A j
  exact GlobalTheory.exists_pelUnif_pow hL.globalFns V _ E H t P j
    (GlobalTheory.UnifPower.main hL (GlobalTheory.UnitBallFree.main hL.globalFns hT) V)
    (GlobalTheory.PowDegData.main hL.globalFns V _ P.D j) ⟨A', ⟨pA⟩⟩

end GlobalTheory.PelUnifPowerDvr
