module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem crt_unit (M N : ℕ) [NeZero M] [NeZero N] (h : M.Coprime N) (a : (ZMod M)ˣ) :
    ∃ u : (ZMod (M * N))ˣ, ZMod.unitsMap (Nat.dvd_mul_right M N) u = a ∧
      ZMod.unitsMap (Nat.dvd_mul_left N M) u = 1 := by
  set e := ZMod.chineseRemainder h
  have h1 : ZMod.castHom (Nat.dvd_mul_right M N) (ZMod M) = (RingHom.fst _ _).comp e.toRingHom :=
    Subsingleton.elim _ _
  have h2 : ZMod.castHom (Nat.dvd_mul_left N M) (ZMod N) = (RingHom.snd _ _).comp e.toRingHom :=
    Subsingleton.elim _ _
  refine ⟨Units.map e.symm.toRingHom.toMonoidHom (MulEquiv.prodUnits.symm (a, 1)), ?_, ?_⟩
  · ext
    rw [ZMod.unitsMap_def, h1]
    simp [MulEquiv.prodUnits]
  · ext
    rw [ZMod.unitsMap_def, h2]
    simp [MulEquiv.prodUnits]

theorem UpperTheory.V.Ws.large₂.clsIndep :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (M N : ℕ) [NeZero M] [NeZero N], M.Coprime N → ∀ a : (ZMod M)ˣ,
      ∃ g : G ℚ Ω, Chr.cls ℚ Ω M g = a ∧ ∀ (N' : ℕ) [NeZero N'], N' ∣ N → Chr.cls ℚ Ω N' g = 1 := by
  intro Ω _ _ _ M N _ _ hMN a
  obtain ⟨u, hu1, hu2⟩ := crt_unit M N hMN a
  obtain ⟨g, hg⟩ := (UpperTheory.V.Chr.clsOnto Ω (M * N)).1 u
  have hres := (UpperTheory.V.Chr.clsFacts ℚ Ω (M * N)).2.1
  refine ⟨g, ?_, ?_⟩
  · rw [← hres M (Nat.dvd_mul_right M N), MonoidHom.comp_apply, hg, hu1]
  · intro N' _ hN'
    rw [← hres N' (hN'.trans (Nat.dvd_mul_left N M)), MonoidHom.comp_apply, hg,
      ← ZMod.unitsMap_comp hN' (Nat.dvd_mul_left N M), MonoidHom.comp_apply, hu2, map_one]
