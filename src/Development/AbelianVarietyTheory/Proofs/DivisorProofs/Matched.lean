module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PinchLift

def GenOn {Y : Scheme.{0}} (L : LB Y) (O : Y.Opens) (s : ∀ k, Γ(Y, L.U k ⊓ O)ˣ) : Prop :=
  ∀ (k l : L.ι) (y : Y), y ∈ L.U k → y ∈ L.U l → y ∈ O →
    gm (𝟙 Y) y (L.U k ⊓ O) (s k) = gm (𝟙 Y) y (L.U k ⊓ L.U l) (L.g k l) * gm (𝟙 Y) y (L.U l ⊓ O) (s l)

def Matched {X' Z Z' : Scheme.{0}} (i' : Z' ⟶ X') (p' : Z' ⟶ Z) (L' : LB X') (LZ : LB Z)
    (w : LB.Iso (L'.pull i') (LZ.pull p')) (O' : X'.Opens) (OZ : Z.Opens) (s' : ∀ k, Γ(X', L'.U k ⊓ O')ˣ)
    (sZ : ∀ j, Γ(Z, LZ.U j ⊓ OZ)ˣ) : Prop :=
  ∀ (z : Z') (j : LZ.ι) (k : L'.ι), p' z ∈ LZ.U j → i' z ∈ L'.U k → p' z ∈ OZ → i' z ∈ O' →
    gm p' z (LZ.U j ⊓ OZ) (sZ j) =
      gm (𝟙 Z') z ((LZ.pull p').U (fun _ => j) ⊓ (L'.pull i').U (fun _ => k)) (w.s (fun _ => j, fun _ => k)) *
        gm i' z (L'.U k ⊓ O') (s' k)

end GlobalTheory.PinchLift
