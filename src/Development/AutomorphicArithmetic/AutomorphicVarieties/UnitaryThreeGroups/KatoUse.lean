module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg

namespace UpperTheory.V.U3

structure CohInp : Prop where
  loc : Loc.LocalPublishedTheorems
  pt : GlobalTheory.Published.PoitouTateNormalised
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  lemK : ∃ CK : ℝ, LemmaK CK

def PropGK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ c₅ A : ℕ,
    ∀ (e N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (p : ℕ), 1 ≤ e → p.Prime → ¬ p ∣ 30 * N * (discr K).natAbs →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c₅ * Nat.totient H.index * ((N : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] (l : ℕ) [Fact l.Prime], l ≠ p →
        ∀ c : Coef l, (∃ ψ ∈ orb c H, GD Ω K l e ψ) →
          (∀ ψ ∈ orb c H, Vlen Ω c e ψ ≠ ⊤) ∧ ∑ ψ ∈ orb c H, Vn Ω c e ψ ≤ 2 * (padicValInt l NN : ℝ)

def CorGK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ c₅ A : ℕ,
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    (e N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (p p' : ℕ), p.Prime → p'.Prime → p ≠ p' →
    ¬ p ∣ 30 * N * (discr K).natAbs → ¬ p' ∣ 30 * N * (discr K).natAbs →
    ∀ (c : ∀ l : Nat.Primes, Coef l) (Ls : Finset Nat.Primes), (∀ l ∈ Ls, ∃ ψ ∈ orb (c l) H, GD Ω K l e ψ) →
      (∀ l ∈ Ls, ∀ ψ ∈ orb (c l) H, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ ≤
        2 * c₅ * (Nat.totient H.index) * ((N : ℝ) * (e + 1)) ^ A * (Real.log p + Real.log p')

end UpperTheory.V.U3

end
