module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Em0Injective
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.GramInvSmul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.IncMInvmul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalUnitExistence.InclusionFromRowsIdentityZero
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexb

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {n : ℕ}

theorem iwa_transport {B : Base F E} (hσ : ∀ z, σ (σ z) = z) {Y Y₀ : Spc F E n} {b b₀ : GL (Fin n ⊕ Fin n) E}
    {ε ε₀ : ℤˣ} (hb : IsFrame2 σ Y b) (hb₀ : IsFrame2 σ Y₀ b₀) (he : b.1ᵀ * dbl Y.J * b.1.map σ = Ald.jeps n ε)
    (he₀ : b₀.1ᵀ * dbl Y₀.J * b₀.1.map σ = Ald.jeps n ε₀) (r : (AE F E)ˣ)
    (hr : ((ε : ℤ) : AE F E) * cA σ (r : AE F E) = ((ε₀ : ℤ) : AE F E) * (r : AE F E))
    (hrf : ∀ v, compFin F E v (r : AE F E) ∈ intLoc F E v ∧ compFin F E v ((r⁻¹ : (AE F E)ˣ) : AE F E) ∈ intLoc F E v)
    (hri : ∀ w, ‖piInf (B.emb w) (r : AE F E)‖ = 1) {K₀ : Subgroup (G2 σ Y₀)} (hK₀ : IsStdK (σ := σ) (Y := Y₀) B b₀ K₀)
    (hI : ∀ x : G2 σ Y₀, ∃ p t, IsPar p t ∧ ∃ k ∈ K₀, x = p * k) {K : Subgroup (G2 σ Y)}
    (hK : IsStdK (σ := σ) (Y := Y) B b K) : ∀ x : G2 σ Y, ∃ p t, IsPar p t ∧ ∃ k ∈ K, x = p * k := by
  have hM := MU_gram (F := F) he he₀ r hr
  have hM' := gram_inv_smul (cA σ) (MU b b₀ r) r hM
  intro x
  let y : G2 σ Y₀ := cj (cA σ) (MU b b₀ r)⁻¹ ((r⁻¹ : (AE F E)ˣ) : AE F E) hM' x
  obtain ⟨p₀, t₀, hp₀, k₀, hk₀, hy⟩ := hI y
  have hx : x = cj (cA σ) (MU b b₀ r) (r : AE F E) hM y := Subtype.ext (by simp only [y, cj_val]; group)
  rw [hy, cj_mul] at hx
  obtain ⟨hpf, -⟩ := par_to hb₀ hp₀
  have hpf' : ParF b (cj (cA σ) (MU b b₀ r) (r : AE F E) hM p₀ : G2 σ Y) := by
    unfold ParF
    rw [inFrame_cj]
    ext i j
    have := congrFun (congrFun hpf i) j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this ⊢
    rw [dg_entry, this, mul_zero, zero_mul]
  obtain ⟨t, ht, -⟩ := par_of hb hpf'
  refine ⟨_, t, ht, _, ?_, hx⟩
  obtain ⟨harch, hfin⟩ := (hK₀ k₀).1 hk₀
  refine (hK _).2 ⟨fun w => ?_, ?_⟩
  · rw [inFrame_cj]; exact dg_arch r _ (hri w) _ (harch w)
  · rintro k' (rfl | rfl) i j
    · rw [inFrame_cj]; exact dg_fin r hrf _ (hfin k₀ (Set.mem_insert _ _)) i j
    · rw [← cj_inv, inFrame_cj]; exact dg_fin r hrf _ (hfin k₀⁻¹ (Set.mem_insert_of_mem _ rfl)) i j

end PositivityTheory.SiegelWeilFormula.Ldexb

end
