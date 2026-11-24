module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem sum_map {ι α : Type} [Fintype ι] (f : α → α) (C : ι → Multiset α) :
    ∑ i, (C i).map f = (∑ i, C i).map f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Multiset.coe_mapAddMonoidHom, map_sum]

private theorem sat_twist {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CG E a) {w : Pl E}
    {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

theorem UpperTheory.V.Cj.S.suppTwist :
    UpperTheory.V.Cj.S.SuppTwist := by
  rintro E _ _ _ a k m B ⟨ι, _, n, π, μ, hk, hn, ha, hμ, hm, hB⟩ x ν hν
  refine ⟨ι, inferInstance, n, fun i => (π i).twist ν, fun i t => (μ i t).map (· + (x : ℂ)), hk, hn, ha,
    fun i t => ?_, fun t => ?_, hB.mono ?_⟩
  · have h := (hμ i t).twist ν
    rwa [(InfType.expo_of_infType E ν).2.1 x hν t] at h
  · rw [sum_map, hm]
  · rintro w ⟨C, hC, hs⟩
    exact ⟨fun i => (C i).map (· * ν.val w), fun i => sat_twist _ (hC i) (hν.1 w), by rw [sum_map, hs]⟩
