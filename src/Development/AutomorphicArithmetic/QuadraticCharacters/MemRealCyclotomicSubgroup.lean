module

public import Development.AutomorphicArithmetic.QuadraticCharacters.LogDerivAtOne
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.QuadraticCharacters.PreHostA

@[expose] public section

namespace HostParam

namespace AbField

variable (E : AbField)

end AbField

structure Core where
  e : ℕ
  two_le_e : 2 ≤ e
  E : AbField
  not_real : ¬ E.IsReal
  d : ℕ
  d_prime : d.Prime
  d_mod : d % 16 = 7
  d_dvd : d ∣ E.N
  K_le : E.chOf d d_dvd ∈ E.chars
  card_inertia_d : Nat.card (E.inertia d) = 2
  ps : DirichletCharacter ℂ E.N
  ps_mem : ps ∈ E.chars
  ps_ne_one : ps ≠ 1
  ps_sq : ps ^ 2 = 1
  ps_odd : ps.Odd
  ps_inertia : ∀ u ∈ E.inertiaUnits d, ps (u : ZMod E.N) = 1
  four_n_dvd : 4 * 2 ^ e ∣ E.N
  attached_subfield_le_adjoin_simple : ∀ u ∈ E.H, ZMod.unitsMap four_n_dvd u = 1 ∨ ZMod.unitsMap four_n_dvd u = -1
  A0 : Subgroup E.Gal
  base_exponent_le_a : A0 ≤ (E.toGalChar (E.chOf d d_dvd) K_le).ker ⊓ (E.toGalChar ps ps_mem).ker
  A0_inf_stabilizer_trivial : ∀ u : (ZMod E.N)ˣ, E.res u ∈ A0 →
    (QuotientGroup.mk (ZMod.unitsMap four_n_dvd u) : GalRealCyclotomic (2 ^ e)) = 1 → E.res u = 1
  split_ram : ∀ l : ℕ, l.Prime → l ≠ d → E.Ramified l → SplitsIn d l

namespace Core

variable (C : Core)



end Core

end HostParam
