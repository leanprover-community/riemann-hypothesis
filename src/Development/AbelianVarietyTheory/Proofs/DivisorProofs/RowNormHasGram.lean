module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CnormMapConjMulVec
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section



noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.GramPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem embedding_eq_or {K : Type} [Field K] (σ₀ : K →+* ℂ) (v : InfinitePlace K) :
    (∀ a, sgAt σ₀ v a = v.embedding a) ∨ ∀ a, sgAt σ₀ v a = starRingEnd ℂ (v.embedding a) := by
  by_cases hv : v = InfinitePlace.mk σ₀
  · rw [sgAt_mk σ₀ hv]
    rcases InfinitePlace.embedding_mk_eq σ₀ with h | h
    · exact Or.inl fun a => by rw [hv, h]
    · exact Or.inr fun a => by rw [hv, h]; simp
  · exact Or.inl fun a => by simp [sgAt, hv]

theorem hasGram_of_unif {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hU : R.LUnif) (i : Fin D.R.m) :
    HasGram (nrmR R i) := by
  refine GlobalTheory.HSApp.hasGram_of_inner _ _ _ fun v => ?_
  refine ⟨(R.HW i (sgAt D.what₂.embLL v)).H, inferInstance, inferInstance,
    ((R.FW i).j (sgAt D.what₂.embLL v)).toAddMonoidHom, ?_, fun x => ?_, fun n e he => (hU i _).1 n e he⟩
  · refine (embedding_eq_or D.what₂.embLL v).imp (fun h a x => ?_) fun h a x => ?_
    · rw [← h]; exact map_smulₛₗ ((R.FW i).j (sgAt D.what₂.embLL v)) a x
    · rw [← h]; exact map_smulₛₗ ((R.FW i).j (sgAt D.what₂.embLL v)) a x
  · unfold nrmR
    rw [InfinitePlace.mk_embedding]
    rfl

end GlobalTheory.CovTop.GramPt

end
