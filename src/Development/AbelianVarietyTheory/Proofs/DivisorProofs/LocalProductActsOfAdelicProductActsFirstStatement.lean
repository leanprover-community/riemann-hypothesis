module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirst
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  first | exact @GlobalTheory.BoxAct.boxFun_acts | exact GlobalTheory.BoxAct.boxFun_acts | (intros; apply GlobalTheory.BoxAct.boxFun_acts <;> assumption)
