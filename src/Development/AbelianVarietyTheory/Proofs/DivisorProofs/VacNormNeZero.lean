module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumNorm

theorem vacNorm_ne_zero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
    Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) t0 → ∀ a d : ℕ, vacNorm D cc δ t0 a d ≠ 0 :=
  fun D cc δ t0 hc ht _ _ =>
    pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ t0 hc ht)

end GlobalTheory.VacuumNorm
