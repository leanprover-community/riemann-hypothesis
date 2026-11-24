module

public import Development.EtaleCohomology.CohomologicalPurity.LeafBdCut
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

theorem pb_v {R : Type} [CommRing R] {A B I : Cx R} (f : A ⟶ B) {n : ℤ} (c : Cochain B I n) (p q : ℤ) (hpq : p + n = q) :
    (pb f c).v p q hpq = f.f p ≫ c.v p q hpq := by
  simp [pb, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

theorem LeafGood_of : LeafGood := by
  intro R _ A B D i l r I hm hp hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro p
    simpa using (hp p).w
  · intro n a
    refine ⟨Cochain.mk (fun p q hpq => Injective.factorThru (a.v p q hpq) (i.f p)), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [pb_v]
    simp [Cochain.mk_v]
  · intro n c c' h
    refine ⟨Cochain.mk (fun p q hpq => (hp p).desc (c.v p q hpq) (c'.v p q hpq) (by
      have := congrArg (fun x => x.v p q hpq) h
      simpa only [pb_v] using this)), ?_, ?_⟩
    · refine Cochain.ext _ _ (fun p q hpq => ?_); rw [pb_v]; simp [Cochain.mk_v]
    · refine Cochain.ext _ _ (fun p q hpq => ?_); rw [pb_v]; simp [Cochain.mk_v]
  · intro n b b' h1 h2
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    apply (hp p).hom_ext
    · have := congrArg (fun x => x.v p q hpq) h1
      simpa only [pb_v] using this
    · have := congrArg (fun x => x.v p q hpq) h2
      simpa only [pb_v] using this

end LateralTheory.CohomologicalPurity.Bd
