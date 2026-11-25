module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import GroundTheory.GlobalFields.Adele.WeakApprox
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField WithZeroMulInt WithZero Topology Filter

noncomputable section

namespace SemiLocal

variable {L : Type*} [Field L] [NumberField L]

theorem denseRange_algebraMap_pi {ι : Type*} [Finite ι] (w : ι → HeightOneSpectrum (𝓞 L))
    (hw : Function.Injective w) :
    DenseRange (fun x : L ↦ fun i ↦ algebraMap L ((w i).adicCompletion L) x) := by
  classical
  let := Fintype.ofFinite ι
  let S := Finset.univ.map ⟨w, hw⟩
  let indexEquiv : ι ≃ S := (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans
    (Finset.univ.equivMap ⟨w, hw⟩)
  let reindex := (Homeomorph.piCongrLeft (Y := fun v : S ↦ v.1.adicCompletion L) indexEquiv).symm
  have h := denseRange_algebraMap_prod_pi S (∅ : Finset (InfinitePlace L))
  exact reindex.surjective.denseRange.comp (Prod.fst_surjective.denseRange.comp h continuous_fst)
    reindex.continuous

end SemiLocal

end

end GroundTheory.Global
