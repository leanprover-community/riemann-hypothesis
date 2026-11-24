module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
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

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

theorem UpperTheory.Gal.G1.pHenselV :
    HenselV := by
  intro F _ _ v f a₀ hf h0 h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (v.adicCompletionIntegers F) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers F)
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F))
  obtain ⟨a, ha, hm⟩ := HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) f hf a₀
    (by rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h0)
    (h1.map (Ideal.Quotient.mk _))
  refine ⟨a, ha, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm
