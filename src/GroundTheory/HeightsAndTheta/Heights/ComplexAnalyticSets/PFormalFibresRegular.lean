module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegular
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibreQuotient
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormalFibresRegularPolynomial
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
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem FormalFibresRegular.proof (hQ : FormalFibreQuotient.Statement)
    (hP : FormalFibresRegularPolynomial.Statement) : FormalFibresRegular.Statement := by
  intro k A _ _ _ hA m hm P _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  have hfs : Function.Surjective (f : MvPolynomial (Fin n) k →+* A) := hf
  obtain ⟨P', -, ⟨e⟩⟩ :=
    hQ (MvPolynomial (Fin n) k) A (f : MvPolynomial (Fin n) k →+* A) hfs inferInstance m P
  have hM : (m.comap (f : MvPolynomial (Fin n) k →+* A)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hfs (H := hm)
  have := hP k n _ hM P'.asIdeal
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
