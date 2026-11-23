module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSkewHermitianCorrectionOfLocalSoluti
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

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix


theorem _root_.GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n : ℕ) (X : Spc F E n) (v : Pl (F := F)) (O : Type) [CommRing O] (c : O →+* O) (ι : O →ₙ+* _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (P Q : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (ι 1) → (∀ y : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) y → ι 1 * y = y) → (∀ x, cA σ (ι x) = ι (c x)) →
    P * Q = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) → Q * P = ι 1 • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) →
    ι 1 • P = P → ι 1 • Q = Q → Pᵀ * incM F X.J * P.map (cA σ) = JL.map ι →
    (∀ z : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt X v ↔ ∃ a : Fin n → O, z = P *ᵥ fun i => ι (a i)) →
    ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O)
      (ZL : Matrix (Fin n) (Fin n) O),
    At (evFin F v) (M - 1) → M * Matrix.fromBlocks P 0 0 P = Matrix.fromBlocks P 0 0 P * G.map ι →
    ZLᵀ * JL + JL * ZL.map c = 0 →
    IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * ZL).det →
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧
      (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * M * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  first | exact @GlobalTheory.TransportBack.transport_back | exact GlobalTheory.TransportBack.transport_back | (intros; apply GlobalTheory.TransportBack.transport_back <;> assumption)
