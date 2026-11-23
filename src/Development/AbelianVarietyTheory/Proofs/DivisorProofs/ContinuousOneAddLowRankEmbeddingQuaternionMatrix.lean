module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory

theorem emb_qm_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : F) (M : ℕ) (A : Matrix (Fin M) (Fin 2) (AF F ⊗[F] E)) (B : Matrix (Fin 2) (Fin M) (AF F ⊗[F] E)) (θ : AF F ⊗[F] E), Continuous fun x : DA F a b => emb A B (qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x) := by
  intro F E _ _ _ _ a b M A B θ
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := IsModuleTopology.topologicalAddGroup (AF F) _
  have hL : ∀ c : AF F ⊗[F] E, Continuous (fun y : AF F ⊗[F] E => c * y) := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulLeft (AF F) c)
  have hR : ∀ c : AF F ⊗[F] E, Continuous (fun y : AF F ⊗[F] E => y * c) := fun c =>
    IsModuleTopology.continuous_of_linearMap (LinearMap.mulRight (AF F) c)
  have hι : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  have hc : ∀ i, Continuous fun x : DA F a b => coords x i := fun i =>
    (continuous_apply i).comp continuous_induced_dom
  have h0 : Continuous fun x : DA F a b => x.re := by simpa [coords] using hc 0
  have h1 : Continuous fun x : DA F a b => x.imI := by simpa [coords] using hc 1
  have h2 : Continuous fun x : DA F a b => x.imJ := by simpa [coords] using hc 2
  have h3 : Continuous fun x : DA F a b => x.imK := by simpa [coords] using hc 3
  have hq : ∀ k l, Continuous fun x : DA F a b => qm (algebraMap (AF F) (AF F ⊗[F] E)) θ x k l := by
    intro k l
    fin_cases k <;> fin_cases l <;> simp [qm]
    · exact (hι.comp h0).add ((hR θ).comp (hι.comp h1))
    · exact (hL _).comp ((hι.comp h2).add ((hR θ).comp (hι.comp h3)))
    · exact (hι.comp h2).sub ((hR θ).comp (hι.comp h3))
    · exact (hι.comp h0).sub ((hR θ).comp (hι.comp h1))
  apply continuous_matrix
  intro i j
  simp only [emb, Matrix.add_apply, Matrix.mul_apply, Matrix.sub_apply]
  refine continuous_const.add (continuous_finsetSum _ fun l _ => (hR _).comp
    (continuous_finsetSum _ fun k _ => (hL _).comp ((hq k l).sub continuous_const)))

end GlobalTheory
