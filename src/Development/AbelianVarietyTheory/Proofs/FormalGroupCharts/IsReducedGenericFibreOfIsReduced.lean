module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Basic
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
public import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isReduced_genericFibre_of_isReduced :
    ∀ (O C Q : Type) [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
      [CommRing Q] [Algebra O Q], IsReduced Q → IsReduced (C ⊗[O] Q) := by
  intro O C Q _ _ _ _ _ _ _ h
  letI : Algebra Q (C ⊗[O] Q) := Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Q (nonZeroDivisors O)) (C ⊗[O] Q) :=
    IsLocalization.tensorRight C (nonZeroDivisors O)
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid Q (nonZeroDivisors O))
    (C ⊗[O] Q) h

end GlobalTheory
