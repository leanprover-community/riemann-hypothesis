module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocOpLin

theorem acts_lin : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl (F := F)) (Op : Module.End ℂ ((κ → AF F) → ℂ)) (c : ℂ)
    (φ φ' η η' ζ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → φ' ∈ SB (κ → Fv F v) →
    Acts (evFin F v) Op φ η → Acts (evFin F v) Op φ' η' → Acts (evFin F v) Op (c • φ + φ') ζ → ζ = c • η + η' := by
  intro F _ _ κ _ v Op c φ φ' η η' ζ hφ hφ' h₁ h₂ h₃
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  have hs : c • φ + φ' ∈ SB (κ → Fv F v) := add_mem ((SB _).smul_mem c hφ) hφ'
  have e : ∀ α β : (κ → Fv F v) → ℂ, tens (evFin F v) (c • α + β) R =
      c • tens (evFin F v) α R + tens (evFin F v) β R := by
    intro α β
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key : tens (evFin F v) ζ R = tens (evFin F v) (c • η + η') R := by
    rw [← h₃ R (hR _ hs), e, map_add (f := _), map_smul, h₁ R (hR φ hφ), h₂ R (hR φ' hφ'), e]
  funext y
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
    intro u' hu'
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (y i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this

end GlobalTheory.LocOpLin
