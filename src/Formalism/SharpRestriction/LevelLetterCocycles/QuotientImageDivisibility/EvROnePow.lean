module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.XAddOneMonic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Formalism.SharpRestriction.LevelLetterCocycles.NatCastEqZeroOfNotDvd
import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section SlopeTestRemainingChoices

variable {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  (p : ℕ) [Fact p.Prime] (m : ℕ) (hlm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
  {F : Type} [Field F] [Algebra O F]

omit [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
theorem root_Zp {y : F} (hy : (1 + y) ^ (p ^ m) = 1) : Polynomial.aeval y (Zp (O := O) p m) = 0 := by
  simp only [Zp, map_sub, map_pow, map_add (f := _), map_one, Polynomial.aeval_X, hy, sub_self]

theorem evR_congr {x x' : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0)
    (hx' : Polynomial.aeval x' (Zp (O := O) p m) = 0) (h : x = x') (f : PowerSeries O) :
    evR p m hlm hx f = evR p m hlm hx' f := by
  subst h
  rfl

theorem evR_eq_cc {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (hx0 : x = 0)
    (f : PowerSeries O) : evR p m hlm hx f = algebraMap O F (PowerSeries.constantCoeff f) := by
  subst hx0
  obtain ⟨q, hq⟩ : ∃ q, f = Zs p m * q + ((f %ʷ Zs p m : Polynomial O) : PowerSeries O) :=
    ⟨_, (f.isWeierstrassDivision_weierstrassDiv_weierstrassMod (Zs_res_ne p m hlm)).eq_mul_add⟩
  show evP p m 0 f = _
  rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx f q _ hq]
  conv_rhs => rw [hq]
  rw [← Polynomial.coeff_zero_eq_aeval_zero']
  simp [Zs]

theorem evR_onePow {x : F} (hx : Polynomial.aeval x (Zp (O := O) p m) = 0) (k : ℕ) :
    evR p m hlm hx ((1 + PowerSeries.X) ^ k) = (1 + x) ^ k := by
  have hX : evR p m hlm hx PowerSeries.X = x := by
    show evP p m x PowerSeries.X = x
    rw [evalWeierstrassMod_eq_aeval_of_eq p m hlm hx PowerSeries.X 0 Polynomial.X (by simp)]
    simp
  rw [map_pow, map_add (f := _), map_one, hX]

end SlopeTestRemainingChoices

theorem exists_prim {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (N : ℕ) (hN : 0 < N) :
    ∃ ζ : F, IsPrimitiveRoot ζ N := by
  haveI : NeZero (N : F) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N F) (by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 hN).ne')
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
