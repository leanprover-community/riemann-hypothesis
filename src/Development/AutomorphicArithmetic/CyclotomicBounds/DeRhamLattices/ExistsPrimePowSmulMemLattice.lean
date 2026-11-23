module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LatticePowerSmul
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per



private theorem UpperTheory.KN.exists_pow_smul_mem_lattice_alt {l : ℕ} [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T :=
  _root_.UpperTheory.Reformulated.B.LatticePowerSmul.exists_pow_smul_mem_lattice_alt LL T v

theorem _root_.UpperTheory.KN.exists_prime_pow_smul_mem_lattice :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (v : T.V), ∃ (n : ℕ) (x : ↥T.L.T), (x : T.V) = ((l : ℚ_[l]) ^ n) • v := by
  intro l _ LL T v
  obtain ⟨n, hn⟩ := UpperTheory.KN.exists_pow_smul_mem_lattice_alt LL T v
  refine ⟨n, ⟨_, hn⟩, ?_⟩
  rw [← algebraMap_smul ↥LL.1 ((l : ℚ_[l]) ^ n) v, map_pow, map_natCast]
