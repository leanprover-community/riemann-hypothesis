module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.liftEx :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], (∀ b : (ZMod N)ˣ, ∃ σ : Ω ≃+* Ω, CycLift N b σ) ∧ ∀ σ : Ω ≃+* Ω, ∃ b : (ZMod N)ˣ, CycLift N b σ := by
  intro E Ω _ _ _ _ _ N _
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have hN : NeZero (N : Ω) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hpos : 0 < N := NeZero.pos N
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N Ω) (Polynomial.degree_cyclotomic_pos N Ω hpos).ne'
  have hζp : IsPrimitiveRoot ζ N := Polynomial.isRoot_cyclotomic_iff.mp hζ
  constructor
  · intro b
    have hx : IsPrimitiveRoot (ζ ^ (b : ZMod N).val) N := hζp.pow_of_coprime _ (ZMod.val_coe_unit_coprime b)
    have hmin : minpoly ℚ ζ = Polynomial.cyclotomic N ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hζp hpos).symm
    have hev : Polynomial.aeval (ζ ^ (b : ZMod N).val) (minpoly ℚ ζ) = 0 := by
      rw [hmin, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
      exact Polynomial.isRoot_cyclotomic_iff.mpr hx
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic ζ) hev
    refine ⟨σ.toRingEquiv, fun x hxN => ?_⟩
    obtain ⟨k, -, rfl⟩ := hζp.eq_pow_of_pow_eq_one hxN
    show σ (ζ ^ k) = (ζ ^ k) ^ (b : ZMod N).val
    rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]
  · intro σ
    have h1 : IsPrimitiveRoot (σ ζ) N := hζp.map_of_injective σ.injective
    obtain ⟨i, hi, hiζ⟩ := hζp.eq_pow_of_pow_eq_one h1.pow_eq_one
    have hcop : i.Coprime N := (hζp.pow_iff_coprime hpos i).mp (hiζ ▸ h1)
    refine ⟨ZMod.unitOfCoprime i hcop, fun x hxN => ?_⟩
    obtain ⟨k, -, rfl⟩ := hζp.eq_pow_of_pow_eq_one hxN
    rw [map_pow, ← hiζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast_of_lt hi, ← pow_mul, ← pow_mul, mul_comm]
