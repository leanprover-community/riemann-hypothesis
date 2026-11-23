module

public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledShortLatticeLeOfShortGeneratorBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

theorem _root_.GlobalTheory.T.scaledShortLattice_le_of_shortGenerator_bound : ShortBoundSt → ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (a b : ℕ) (s : 𝓞 T.Q.c.F), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → s = (zOwnP D (T.dδ j w.n).pd w : 𝓞 T.Q.c.F) * nnW (recB h.toLawsCore) hinj EX w * (pPow D a b b : 𝓞 T.Q.c.F) → (recPJ h j hj).Thc s w ≤ (recB h.toLawsCore).Mlat j w := by
  first | exact @GlobalTheory.PlaceTop.thc_le_of_shortBound | exact GlobalTheory.PlaceTop.thc_le_of_shortBound | (intros; apply GlobalTheory.PlaceTop.thc_le_of_shortBound <;> assumption)
