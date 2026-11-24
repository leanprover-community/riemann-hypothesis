module

public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem trace_map_of_adjoin_range_eq_top_of_finrank_eq : ∀ (E L E' L' : Type) [Field E] [Field L] [Algebra E L] [FiniteDimensional E L] [Field E'] [Field L'] [Algebra E' L'] (j : E →+* E') (jL : L →+* L'), (∀ x, jL (algebraMap E L x) = algebraMap E' L' (j x)) → Algebra.adjoin E' (Set.range jL) = ⊤ → Module.finrank E' L' = Module.finrank E L → ∀ z, Algebra.trace E' L' (jL z) = j (Algebra.trace E L z) := by
  intro E L E' L' _ _ _ _ _ _ _ j jL hcomp hadj hrank z
  classical
  set n := Module.finrank E L
  let b : Module.Basis (Fin n) E L := Module.finBasis E L
  have hpos : 0 < Module.finrank E' L' := by rw [hrank]; exact Module.finrank_pos
  haveI : FiniteDimensional E' L' := Module.finite_of_finrank_pos hpos
  let v : Fin n → L' := fun k => jL (b k)
  have hexp : ∀ w : L, jL w = ∑ k, j (b.repr w k) • v k := by
    intro w
    conv_lhs => rw [← b.sum_repr w]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, map_mul, hcomp, ← Algebra.smul_def]
  have hspan : Submodule.span E' (Set.range jL) ≤ Submodule.span E' (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    rw [hexp w]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hadj' : Subalgebra.toSubmodule (Algebra.adjoin E' (Set.range jL)) = Submodule.span E' (Set.range jL) := by
    apply Algebra.adjoin_eq_span_of_subset
    have : (Submonoid.closure (Set.range jL) : Set L') = Set.range jL := by
      have := Submonoid.closure_eq (MonoidHom.mrange (jL : L →* L'))
      simpa using congrArg (fun S : Submonoid L' => (S : Set L')) this
    rw [this]; exact Submodule.subset_span
  have htop : (⊤ : Submodule E' L') ≤ Submodule.span E' (Set.range v) := by
    rw [hadj, Algebra.top_toSubmodule] at hadj'
    rw [hadj']; exact hspan
  let b' : Module.Basis (Fin n) E' L' := basisOfTopLeSpanOfCardEqFinrank v htop (by simp [hrank, n])
  have hb' : ∀ k, b' k = v k := fun k => by simp [b']
  have hrepr : ∀ w : L, ∀ i, b'.repr (jL w) i = j (b.repr w i) := by
    intro w i
    have : jL w = b'.equivFun.symm (fun k => j (b.repr w k)) := by
      rw [Module.Basis.equivFun_symm_apply, hexp w]
      simp [hb']
    rw [← b'.equivFun_apply, this, LinearEquiv.apply_symm_apply]

  rw [Algebra.trace_eq_matrix_trace b', Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, hb', v, ← map_mul, hrepr]

end GlobalTheory
