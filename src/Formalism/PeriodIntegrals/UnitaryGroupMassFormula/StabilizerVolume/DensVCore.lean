module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVNA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.CosDens
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVGlue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

def GramFilt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (a : ℕ), 1 ≤ a → a + 2 ≤ M → ∀ (v : HeightOneSpectrum (𝓞 F)) (d : ℕ) (b : Module.Basis (Fin d) F E)
      (x : Fin a → Fin M → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) x →
      ∃ N ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E), ∀ y, y - x ∈ N →
        ∀ Λ0, scaledB (Fv F v) (latSub b v a M) Λ0 →
          (Λ0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)) ⊆ N →
        ∃ (Λ : ℕ → AddSubgroup (Fin a → Fin M → Fv F v ⊗[F] E))
          (H : ℕ → AddSubgroup (HermR (Fv F v) σ a))
          (D : (Fin a → Fin M → Fv F v ⊗[F] E) →+ HermR (Fv F v) σ a),
          Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧
          (∀ n, IsCompact (Λ n : Set (Fin a → Fin M → Fv F v ⊗[F] E))) ∧ Antitone Λ ∧
          (∀ n, IsOpen (H n : Set (HermR (Fv F v) σ a))) ∧
          (∀ n, IsCompact (H n : Set (HermR (Fv F v) σ a))) ∧
          (∀ N' ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ n, (H n : Set (HermR (Fv F v) σ a)) ⊆ N') ∧
          (∀ n, (Λ n).map D = H n) ∧
          ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n,
            gramH (Fv F v) σ hσ J hJ (y + Z + W) - gramH (Fv F v) σ hσ J hJ (y + Z) - D W ∈
              H (n + 1)

theorem densVLat_of (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensVLat := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨_t1, t2, t3, _t4, t5, _t6, _t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hCM.2.2.2
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  intro d b x hx
  obtain ⟨N, hN, hd⟩ := hF F E σ hσ M J hJ.1 hJ.2 a h1 (by omega) v d b x hx
  refine ⟨N, hN, fun y hy Λ0 hB _ _ hsub => ?_⟩
  obtain ⟨Λ, H, D, h0, hΛo, hΛc, hΛa, hHo, hHc, hHb, hD, hyp⟩ := hd y hy Λ0 hB hsub
  subst h0
  exact densCos_of_filt hP1 hP2 μv νv (gramR (Fv F v) σ J) Subtype.val Subtype.val_injective
    (gramH (Fv F v) σ hσ J hJ.1) (Continuous.subtype_mk t5 _) (fun _ => rfl) y Λ H hΛo hΛc hΛa
    hHo hHc hHb D hD hyp

theorem densV_of_filt (hP1 : HenselCount) (hP2 : CosDens) (hT : TensAll) (hF : GramFilt) :
    DensV :=
  densV_of_lat hT (densVLat_of hP1 hP2 hT hF)

end PI.VolStabS
