module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

open UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem hull_stable {T : Module.End ℂ (Sm E a)} (hT : T ∈ Comm E a) (S : Submodule ℂ (Sm E a)) :
    ∀ φ ∈ hull S, T φ ∈ hull S := by
  have : hull S ≤ (hull S).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨T', hT', φ, hφ, rfl⟩
    exact Submodule.subset_span ⟨T * T', ⟨fun k => (hT.1 k).mul_left (hT'.1 k),
      fun z hz => (hT.2.1 z hz).mul_left (hT'.2.1 z hz), fun ψ h => hT.2.2 _ (hT'.2.2 ψ h)⟩, φ, hφ, rfl⟩
  exact fun φ hφ => this hφ

private theorem aut_cap (t : E →+* ℂ) (u : ℂ) (φ : Sm E a) (h : IsAutForm φ) : IsAutForm (cap t u φ) := by
  obtain ⟨p, -, q, -, e⟩ := Cm.mem_Zalg_iff.1 (Cm.cap_mem_Zalg (a := a) t u)
  obtain ⟨ψ, rfl⟩ := Cm.mem_range_ofAut.2 h
  refine Cm.mem_range_ofAut.1 ⟨GroundTheory.Automorphic.AutomorphicForm.uActionAF E a p ψ +
    Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E a q ψ, ?_⟩
  rw [e, map_add (f := _), map_smul]
  rfl

private theorem smEq_fin (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    Cm.smEq E a (finRep E a g φ) = GroundTheory.Automorphic.AutomorphicForm.rtFin g (Cm.smEq E a φ) :=
  Subtype.ext (funext fun x => (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (x * f g)) Fb.finEmb_eq).symm)

private theorem fin_mem (g : GL (Fin a) (Af E)) : finRep E a g ∈ Comm E a := by
  refine ⟨fun k => ?_, fun z _ => ?_, fun φ h => ?_⟩
  · exact Commute.map (show Commute (finGL E a g) (infGL E a (Unitary.toUnits k)) from (infGL_comm _ _).symm) (rt E a)
  · refine LinearMap.ext fun φ => (Cm.smEq E a).injective ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, smEq_fin, Cm.smEq_uTC, Cm.smEq_uTC, smEq_fin,
      GroundTheory.Automorphic.AutomorphicForm.uAction_rtFin]
  · refine (Cm.isAutForm_iff _).2 ?_
    rw [← Cm.coe_smEq, smEq_fin]
    exact ((Cm.isAutForm_iff _).1 h).rightTranslate_finEmb g

end

theorem UpperTheory.V.Cj.S.hullOps :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.HullOps := by
  intro hc E _ _ _ a S
  refine ⟨fun φ hφ => Submodule.subset_span ⟨1, ⟨fun _ => Commute.one_left _, fun _ _ => Commute.one_left _,
    fun _ h => h⟩, φ, hφ, rfl⟩, fun t u => hull_stable ⟨fun k => (hc E a t u).2.1 (.cpt k),
      fun z _ => (hc E a t u).2.2.1 z, aut_cap t u⟩ S, fun g => hull_stable (fin_mem g) S⟩
