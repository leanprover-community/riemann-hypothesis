module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseKPair
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseStmtX
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBoxFinC
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxSec
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



section
noncomputable section
namespace GlobalTheory.ThK.Dbl.Box
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl.Dense
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}
variable {A : Spc F E m} {Y : Spc F E n} {B : Base F E}
theorem _root_.GlobalTheory.ThK.Dbl.boxSecX_of_k (hL : _root_.GlobalTheory.ThK.Dbl.FinLevel_k) (hC : _root_.GlobalTheory.ThK.Dbl.Stab2Cpt_k) : _root_.GlobalTheory.ThK.Dbl.BoxSecX_k := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hX _ _ hM χ _ _ dd om S l ⟨d', ht, hd⟩ h K a hK _ Φ₁ h1 Φ₂ h2
  have tr : ∀ {p q : ℕ} {u : Matrix (Fin p) (Fin q) (AE F E)}, At (evI F) u → At (evI F) uᵀ := fun hu c hc => by
    rw [← Matrix.transpose_smul, hu c hc, Matrix.transpose_zero]
  refine isSec_of h (polData_kfin hM (fun g₁ s1 g₂ s2 f₁ p1 f₂ p2 => _root_.GlobalTheory.ThK.Dbl.Box.box_kfin_k hL hB hK (hC F E σ B n X r s hB (.inl hX) K hK)
    h.weil.2.1.toIsSplitting hd (fun N n1 n2 => (sInf_le (a := N) ⟨fun f ⟨ε, hε⟩ => n1 ε f fun u u' hu hu' e => ?_,
      fun u hu f hf f₁ e => ?_⟩ : M.Pol B.ψ B.emb ≤ N)) s1 s2 p1 p2) h1 h2)
  · rw [← u.transpose_transpose, ← u'.transpose_transpose, ht, ht]
    refine hε uᵀ u'ᵀ (tr hu) (tr hu') (fun w => ?_) _ _ (actsD_dop M hB.std (tr hu) f) (actsD_dop M hB.std (tr hu') f)
    rw [Matrix.transpose_map, Matrix.transpose_map, e w, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  · rw [actsD_unique' M hB.std hu e]
    have hmem := n2 uᵀ (tr hu) f hf
    rwa [ht] at hmem
end GlobalTheory.ThK.Dbl.Box
end
end
