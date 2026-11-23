module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceTransversalOfLocalCoreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlockStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfSkewUnipotentMemDoubledLatticeStabilizerStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertTransv

theorem exists_unip_corner_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hvw g hg
  obtain ⟨Z, hZs, hZl, hZn, hdet, hinv⟩ := GlobalTheory.T.exists_inertPlace_transversal_of_localCore GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock F E σ B n r s X hB hX v w hvw g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨u, huK, huP, hu⟩ := GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer F E σ n X v h2 Z hZs hZl hZn
  set N : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := GlobalTheory.DblVac.antiCols (F := F) (E := E) n with hN
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hΔ
  have hNN : Nᵀ * N = (2 : AF F) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hN, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have hmul : GlobalTheory.DblVac.matD (g * u) = GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD u := rfl
  have key : Nᵀ * GlobalTheory.DblVac.matD (g * u) * N = Nᵀ * GlobalTheory.DblVac.matD g * N + Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z := by
    rw [hmul, hu]
    have : Nᵀ * (GlobalTheory.DblVac.matD g * (1 + (⅟(2 : AF F)) • (Δ * Z * Nᵀ))) * N =
        Nᵀ * GlobalTheory.DblVac.matD g * N + (⅟(2 : AF F)) • (Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z * (Nᵀ * N)) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, hNN, Matrix.mul_smul, smul_smul, invOf_mul_self, one_smul, Matrix.mul_one]
  refine ⟨u, huK, huP, ?_, ?_⟩
  · convert hdet using 2
    exact congrArg Matrix.det key
  · intro z hz; convert hinv z hz using 3
    exact key

end GlobalTheory.InertTransv
