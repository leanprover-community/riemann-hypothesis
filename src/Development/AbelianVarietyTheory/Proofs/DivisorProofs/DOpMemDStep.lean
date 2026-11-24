module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinHasTemperateGrowth
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
import Mathlib.RingTheory.PiTensorProduct
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

noncomputable section

namespace GlobalTheory.FockKFin

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) : Submodule ℂ (SInf F κ) :=
  Submodule.span ℂ {h | ∃ a b : κ → mixedEmbedding.mixedSpace F, ∃ f ∈ P, h = dOp a b f}

theorem dOp_mem_dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) (a b : κ → mixedEmbedding.mixedSpace F)
    {f : SInf F κ} (hf : f ∈ P) : dOp a b f ∈ dStep P :=
  Submodule.subset_span ⟨a, b, f, hf, rfl⟩

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {g | GaussD M τ g}

def polLe (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (vacSp M τ) (fun _ P => P ⊔ dStep P) m

theorem polLe_zero (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : polLe M τ 0 = vacSp M τ := rfl

theorem polLe_succ (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    polLe M τ (m + 1) = polLe M τ m ⊔ dStep (polLe M τ m) := rfl

theorem polLe_mono (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Monotone (polLe M τ) :=
  monotone_nat_of_le_succ fun m => by rw [polLe_succ]; exact le_sup_left

def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.FockKFin

end
