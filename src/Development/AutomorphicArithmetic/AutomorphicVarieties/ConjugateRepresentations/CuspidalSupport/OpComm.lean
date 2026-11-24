module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
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

private theorem hk_comm_of {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    {K : Subgroup G} (hK : IsCommensurated K) {h : G → ℂ} (hh : h ∈ Hecke ℂ K) (A : Module.End ℂ V)
    (hA : ∀ g, Commute A (ρ g)) (x : V) : A (hkOp ρ hK hh x) = hkOp ρ hK hh (A x) :=
  map_heckeVec hK hh (ρ' := ρ) A (fun g y => LinearMap.congr_fun (hA g).eq y) x

theorem UpperTheory.V.Cj.S.opComm :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.OpComm := by
  intro hC E _ _ _ a T i i' φ hφ
  rcases i with ⟨t, u⟩ | ⟨⟨w, hw⟩, h, hh⟩ <;> rcases i' with ⟨t', u'⟩ | ⟨⟨w', hw'⟩, h', hh'⟩
  · exact LinearMap.congr_fun ((hC E a t u).2.2.2 t' u').eq φ
  · exact hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (cap t u) (fun g => (hC E a t u).1 _) φ
  · exact (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (cap t' u') (fun g => (hC E a t' u').1 _) φ).symm
  · by_cases e : w = w'
    · subst e
      have hK := Final.GLintComm E w a
      change heckeVec (fL a w) (KGL w (n := a)) h (heckeVec (fL a w) (KGL w (n := a)) h' φ) =
        heckeVec (fL a w) (KGL w (n := a)) h' (heckeVec (fL a w) (KGL w (n := a)) h φ)
      rw [← SatCompare.heckeVec_conv hK hh hh' (hφ w hw), ← SatCompare.heckeVec_conv hK hh' hh (hφ w hw),
        Final.HeckeCommGL E w a ℂ h hh h' hh']
    · refine hk_comm_of (fL a w') (Final.GLintComm E w' a) hh' (hkOp (fL a w) (Final.GLintComm E w a) hh)
        (fun g => LinearMap.ext fun y => ?_) φ
      refine (hk_comm_of (fL a w) (Final.GLintComm E w a) hh (fL a w' g) (fun k => ?_) y).symm
      exact Commute.map (LocUniq.comm_locGL w (pLoc_locGL_of_ne e g) k) (finRep E a)
