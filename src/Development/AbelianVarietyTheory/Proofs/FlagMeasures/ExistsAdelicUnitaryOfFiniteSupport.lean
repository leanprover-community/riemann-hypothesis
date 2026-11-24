module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitC
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

theorem exists_adelic_of_finset {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hh : ∀ v, h v ∈ UPts σ J (v.adicCompletion F)) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ x ∈ UPts σ J (Ad F), (∀ v ∈ S, bc (prV (E := E) v) x = h v) ∧
      ∀ v ∉ S, bc (prV (E := E) v) x = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, by simp, fun v _ => map_one _⟩
  | insert w S hw ih =>
    obtain ⟨x, hx, h1, h2⟩ := ih
    have hne : ∀ v, v ≠ w →
        bc (prV (E := E) v) (Formalism.UG.P.afsplitU w (h w) x) = bc (prV (E := E) v) x := fun v hv =>
      Units.ext (Formalism.UG.P.afsplitC_prV_ne w v hv _ _)
    refine ⟨Formalism.UG.P.afsplitU w (h w) x, Formalism.UG.P.afsplitU_mem w σ J _ _ (hh w) hx, ?_, ?_⟩
    · intro v hv
      by_cases e : v = w
      · subst e
        exact Units.ext (Formalism.UG.P.afsplitC_prV v _ _)
      · rw [hne v e]
        exact h1 v ((Finset.mem_insert.1 hv).resolve_left e)
    · intro v hv
      rw [Finset.mem_insert, not_or] at hv
      rw [hne v hv.1]
      exact h2 v hv.2

theorem exists_adelic_of_finite_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (h : ∀ v : HeightOneSpectrum (𝓞 F), GL (Fin n) (E ⊗[F] v.adicCompletion F)), (∀ v, h v ∈ UPts σ J (v.adicCompletion F)) → {v | h v ≠ 1}.Finite → ∃ x ∈ UPts σ J (Ad F), ∀ v, bc (prV (E := E) v) x = h v := by
  intro F E _ _ _ _ _ n σ J h hh hf
  obtain ⟨x, hx, h1, h2⟩ := exists_adelic_of_finset σ J h hh hf.toFinset
  refine ⟨x, hx, fun v => ?_⟩
  by_cases hv : v ∈ hf.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    by_contra e
    exact hv (hf.mem_toFinset.2 fun e' => e e'.symm)

end GlobalTheory.St.G
