module

public import Formalism.HermitianCurvature.StatementJ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix

namespace Formalism.FourierDecayAlt.P.Jx6

end Formalism.FourierDecayAlt.P.Jx6

namespace Formalism.FourierDecayAlt.P

open Jx6

theorem form_gives_theorem_A : Formalism.FourierDecayAlt.J.FormGivesMain := by
  intro hM P _ B hPos he hKV h2A hF hMass hform hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35⟩ := hPos
  have hn : 0 < B.n0c := a33
  have hen : 0 < B.e1 * B.n0c := mul_pos he hn
  have key := hM P { B with supdens := B.e1, KtopV := B.KV / (B.e1 * B.n0c) }
    ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
      a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, he.le, a35⟩ h2A hF
    (by
      constructor
      · show B.KV ≤ B.e1 * B.n0c * (B.KV / (B.e1 * B.n0c))
        rw [mul_div_cancel₀ _ hen.ne']
      · show 0 ≤ B.KV / (B.e1 * B.n0c)
        exact div_nonneg hKV hen.le)
    hMass
    (by show B.e1 ≤ B.e1; exact le_refl _)
    (by
      show B.c0 * B.c0' * (B.KV / (B.e1 * B.n0c)) ≤ (1 + B.δ) * B.IntN
      rw [← mul_div_assoc, div_le_iff₀ hen]
      linarith)
    hJ hNu hInf hVol hLev hMas hCol hOrd hTyp hInd
  exact key

end Formalism.FourierDecayAlt.P
