module

public import Formalism.RealPlaceAnalysis.StatementU
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsoPartStable
import Formalism.RealPlaceAnalysis.QuotientSettingHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunJetApply
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace GlobalTheory.SphJet

theorem vminus_coef : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (Λ : Fin n → ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E Λ u → ∀ F ∈ Vminus ε E Λ u, ∀ a b : Fin n, a ≤ b → ⟪u, arrOf V n 1 F (fun _ => (a, b))⟫_ℂ = 0 := by
  intro V _ _ n ε E Λ u hg hu hΛ F hF a b hab
  have hkr : KRel ε (arrE E 1) := glRel_kRel ε _ ((arrModule V n ε E 1).1 hg).1
  have hku : KUnit ε E := isUnitary_kUnit ε E hu

  let φ : Arr V n 1 →ₗ[ℂ] ℂ :=
    (innerₛₗ ℂ u).comp ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 → Fin n × Fin n => V)
      (fun _ => (a, b))).comp (arrOf V n 1))
  suffices hle : Vminus ε E Λ u ≤ LinearMap.ker φ by
    have h0 : φ F = 0 := hle hF
    simpa [φ] using h0

  refine iSup₂_le fun y hy => ?_
  obtain ⟨-, μ, ⟨c, d, hdc, -, rfl⟩, hyh⟩ := hy
  rw [(kLow _ n ε (arrE E 1) _ y hkr hyh).1]
  refine Submodule.span_le.2 ?_
  rintro z ⟨w, hw, rfl⟩

  obtain ⟨ν, hht, hν⟩ := GlobalTheory.Jet.VminusComp.word_weight hkr hyh.1 w hw
  have hcw := GlobalTheory.Jet.VminusComp.comp_weight hν a b
  have hne : Λ ≠ ν - root a b := by
    intro h
    have h1 := congrArg GlobalTheory.Jet.VminusComp.ht h
    rw [GlobalTheory.Jet.VminusComp.ht_sub, GlobalTheory.Jet.VminusComp.ht_root] at h1
    rw [GlobalTheory.Jet.VminusComp.ht_add, GlobalTheory.Jet.VminusComp.ht_root] at hht
    have h2 : ((d : ℕ) : ℝ) < ((c : ℕ) : ℝ) := by exact_mod_cast hdc
    have h3 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith

  have h0 := kWtOrth V n ε E Λ (ν - root a b) u _ hku hΛ.1 hcw hne
  simpa [φ, arrOf] using h0

end GlobalTheory.SphJet
