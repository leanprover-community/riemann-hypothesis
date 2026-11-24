module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtension
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isUnramifiedAt_of_isUnramifiedInGaloisExtension : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)}, GlobalTheory.NT.UnramIn L 𝔭 → ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) P := by
  first | exact @GlobalTheory.NT.isUnramifiedAt_of_unramIn | exact GlobalTheory.NT.isUnramifiedAt_of_unramIn | (intros; apply GlobalTheory.NT.isUnramifiedAt_of_unramIn <;> assumption)
