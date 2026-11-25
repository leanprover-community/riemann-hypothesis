module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.TautEx

alias toUnit_left := _root_.GlobalTheory.ObjPull.toUnit_left'

section Gen

variable {Y : Scheme.{0}} {M : LB Y}

def mulU (u : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun j => res le_top u * t.s j⟩

end Gen

section Base

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

abbrev fC : Sp (MvPowerSeries (Fin N) W) ⟶ Sp W := spMap MvPowerSeries.C

abbrev Bp : Over (Sp (MvPowerSeries (Fin N) W)) := (Over.pullback (fC (W := W) N)).obj T.B

instance : IsCommMonObj (Bp T N) := (isAb_Bp T N).comm

abbrev cm : CubeMap (Bp T N) T.B := cubeMapOf (cart T N)

abbrev Mp : RigLB (Bp T N) := (cm T N).rigLB T.M (pullSt T N).fst (pullSt T N).snd.fst

abbrev cubP : CubicalStr (Bp T N) (Mp T N) := CubePf.cubical (cm T N) T.M T.cub _ _

end Base

section Periods

variable (W : Type) [CommRing W] [IsDomain W] (N : ℕ)

end Periods

section Charts

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N : ℕ)

end Charts

section Tau

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

alias unitOn_mul := _root_.GlobalTheory.ToricData.unitOn_mul

alias triple_lift_comp_projections := _root_.GlobalTheory.BXOf.onObjOf3_x_eq

end Tau

section Main

variable {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (N m n : ℕ)
  (ε : Fin N → LinearMap.BilinForm ℤ (Fin T.r → ℤ))

end Main

end GlobalTheory.PolDeg.TautEx
