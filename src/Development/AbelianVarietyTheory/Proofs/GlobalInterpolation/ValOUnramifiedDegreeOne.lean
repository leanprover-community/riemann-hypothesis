module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
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
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.LocUnr

variable {K : Type} [Field K] [NumberField K]

theorem valuation_eq_exp_neg_one (P : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (h1 : r ∈ P.asIdeal)
    (h2 : r ∉ P.asIdeal ^ 2) : P.valuation K (algebraMap (𝓞 K) K r) = WithZero.exp (-1 : ℤ) := by
  have e : P.valuation K (algebraMap (𝓞 K) K r) = P.intValuation r := P.valuation_of_algebraMap r
  rw [e]
  have hr : r ≠ 0 := by rintro rfl; exact h2 (Submodule.zero_mem _)
  have a1 := (P.intValuation_le_pow_iff_mem r 1).2 (by simpa using h1)
  have a2 := mt (P.intValuation_le_pow_iff_mem r 2).1 h2
  rw [← WithZero.exp_log (P.intValuation_ne_zero r hr)] at a1 a2 ⊢
  rw [WithZero.exp_le_exp] at a1 a2
  congr 1
  push_cast at a1 a2
  omega

end GlobalTheory.LvT.LocUnr
