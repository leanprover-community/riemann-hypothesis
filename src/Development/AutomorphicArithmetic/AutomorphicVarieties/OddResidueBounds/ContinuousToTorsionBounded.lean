module

public import Formalism.GaloisCohomology.Statement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem continuous_to_torsion_bounded {G : Type} [TopologicalSpace G] [CompactSpace G] (l : ℕ) [Fact l.Prime]
    (f : G → QZ l) (hf : Continuous f) : ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • f g = 0 := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  choose k hk using (UpperTheory.V.Kum.qzBasic l).2.1
  obtain ⟨r, hr⟩ := (hfin.image k).bddAbove
  refine ⟨r, fun g => ?_⟩
  have h1 : k (f g) ≤ r := hr ⟨f g, ⟨g, rfl⟩, rfl⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have h2 : (l : ℤ_[l]) ^ k (f g) • f g = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hk _
  rw [pow_add, mul_smul, h2, smul_zero]

theorem UpperTheory.V.Odd.Z1_H1_qz_twist_l_power_torsion :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), (∀ z : Z1 (qzTw D e), ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧ ∀ x : H1 (qzTw D e), ∃ r : ℕ, (l : ℤ_[l]) ^ r • x = 0 := by
  intro E Ω _ _ _ _ _ l _ D e
  have h : ∀ z : Z1 (qzTw D e), ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0 := fun z =>
    continuous_to_torsion_bounded l z.1 z.2.1
  refine ⟨h, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨r, hr⟩ := h z
  refine ⟨r, ?_⟩
  have hz : (l : ℤ_[l]) ^ r • z = 0 := Subtype.ext (funext hr)
  rw [← Submodule.Quotient.mk_smul, hz, Submodule.Quotient.mk_zero]
