module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledSpaceSplittingConstantHalfRealPlaces
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

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl


theorem _root_.GlobalTheory.T.doubledSpace_splitting_constant_half_realPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (dd : Darboux (symp (R := AF F) (cA σ) (-1) JA (dbl JB)) (κ ⊕ κ)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ)
    (cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → Framed τ JA JB a b A C →
    IsUWeilSplit (cA σ) (adeleClass F) ψ (-1) JA (dbl JB) dd χ (diagCols β) omd → HasExp τ χ m →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ l ∈ (adeleClass F).adm (κ ⊕ κ), (∀ z : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∀ φ ∈ (adeleClass F).sp (κ ⊕ κ),
      l (dd.rho ψ (z * (diagCols β : Matrix (β ⊕ β) β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))ᵀ) φ) = l φ) ∧
      ∃ g ∈ SB (κ ⊕ κ → Af F), ∀ f : SInf F (κ ⊕ κ),
        l (pureA F f g) = ∫ x : κ → mixedEmbedding.mixedSpace F, f (Sum.elim x x)) →
    (∫ x : κ → mixedEmbedding.mixedSpace F, Φd (PiTensorProduct.tprod ℂ fun _ => 1) (Sum.elim x x)) ≠ 0 →
    0 < R + S → ∀ w, cd w = m w / 2 := by
  first | exact @GlobalTheory.RealLift.DConst.cd_eq_half_exp | exact GlobalTheory.RealLift.DConst.cd_eq_half_exp | (intros; apply GlobalTheory.RealLift.DConst.cd_eq_half_exp <;> assumption)
