module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.DifferentElement

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement

theorem mult_ratio (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (l : ℕ) (hl : l.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsPrime) (hlP : (l : 𝓞 E) ∈ P) :
    (multiplicity P (differentIdeal ℤ (𝓞 E)) : ℚ) / (multiplicity P (Ideal.span {(l : 𝓞 E)}) : ℚ) =
      ((NumberField.discr E).natAbs.factorization l : ℚ) / (Module.finrank ℚ E : ℚ) := by
  classical
  have hl0 : (l : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 ((Submodule.mem_bot _).1 hlP)
  have hirr : Irreducible P := (Ideal.prime_of_isPrime hP0 hP).irreducible
  have hd : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero E)
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E l
    ((NumberField.discr E).natAbs.factorization l) (ordCompl[l] (NumberField.discr E).natAbs) hl
    (Nat.not_dvd_ordCompl hl hd) (Nat.ordProj_mul_ordCompl_eq_self _ _).symm P hP hlP
  have hpos := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos E l hl hP hlP
  simp only [multiplicity_eq_count_normalizedFactors hirr, normalize_eq]
  have hn : (Module.finrank ℚ E : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  rw [div_eq_div_iff (by exact_mod_cast hpos.ne') hn]
  convert congrArg (fun t : ℕ => (t : ℚ)) h using 1 <;> push_cast <;> ring

end GlobalTheory.DifferentElement

namespace GlobalTheory.DifferentElement


end GlobalTheory.DifferentElement
