module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SatakeDualWeyl.Statement
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion

@[expose] public section

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem not_mem_of_coprime {p g : ℕ} (h : Nat.Coprime p g) (v : HeightOneSpectrum (𝓞 F))
    (hg : ((g : ℕ) : 𝓞 F) ∈ v.asIdeal) : ((p : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  intro hp
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr h
  have h1 : ((a * p + b * g : ℤ) : 𝓞 F) ∈ v.asIdeal := by
    push_cast
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hp) (v.asIdeal.mul_mem_left _ hg)
  rw [hab, Int.cast_one] at h1
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

variable {σE : E →ₐ[F] E} {J : Matrix (Fin N) (Fin N) E} {gp : Fin 2 → ℕ}
    {splitG : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal →
      E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    {Lb : Submodule (𝓞 E) (Fin N → E)}
    {Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F))} {k m t j : ℕ}

end Formalism.L2.G
