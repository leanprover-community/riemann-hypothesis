module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
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
public import ReciprocityTheory.DualLattices.Imports

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem IsEps.isPrimitiveRoot_untilt {l : ℕ} [hl : Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    IsPrimitiveRoot ((frobeniusEquiv (Per.Fl l) l).symm e).untilt l := by
  have hp : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt ^ l = 1 := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p, h.1]
  have ho := orderOf_eq_prime hp h.2
  have := IsPrimitiveRoot.orderOf ((frobeniusEquiv (Per.Fl l) l).symm e).untilt
  rwa [ho] at this

theorem ker_theta_eq_span_xi {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    RingHom.ker (Per.θ l) = Ideal.span {xi e} := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -⟩ :=
    ReciprocityTheory.PGsh.a0 l ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l)
  exact ((hX e (PadicComplexInt.integers l) h.isPrimitiveRoot_untilt).2.2.2 pf hpf).1

theorem theta_eq_zero_iff_xi_dvd (l : ℕ) [Fact l.Prime] :
    ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  intro e h a
  rw [← RingHom.mem_ker, ker_theta_eq_span_xi h, Ideal.mem_span_singleton]

end GlobalTheory.MemLoc
