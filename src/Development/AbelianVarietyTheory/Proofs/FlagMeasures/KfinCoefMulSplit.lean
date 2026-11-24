module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
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
import Mathlib.RingTheory.Finiteness.Lattice
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

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.KFinCoefSplit

variable {k r : ℕ}

theorem kfin_smul {R : Rep k r} (a : ℂ) {v : R.H} (hv : R.KFin v) : R.KFin (a • v) := by
  obtain ⟨S, hfd, hv, hst⟩ := hv
  exact ⟨S, hfd, S.smul_mem a hv, hst⟩

theorem kfin_sum {R : Rep k r} {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, R.KFin (x c)) :
    R.KFin (∑ c, x c) := by
  choose S hfd hS hst using hx
  refine ⟨⨆ c, S c, inferInstance, Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c (hS c),
    fun g hg y hy => ?_⟩
  have hle : (⨆ c, S c) ≤ (⨆ c, S c).comap (R.σ g : R.H →ₗ[ℂ] R.H) :=
    iSup_le fun c z hz => Submodule.mem_iSup_of_mem c (hst c g hg z hz)
  exact hle hy

theorem kfin_coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (om om' : ι → ℂ) (v v' : R.H), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → R.KFin v → R.KFin v' → (∀ I, (RI I).KFin (∑ c, pr I c (tm R om v c)) ∧ (RI I).KFin (∑ c, pr I c (tm R om' v' c))) ∧ ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R om v c), (RI I).σ g (∑ c, pr I c (tm R om' v' c))⟫_ℂ := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI om om' v v' hR hRI hF hT hv hv'
  obtain ⟨-, -, -, -, hRT, -, hRK, -, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR
  have hadj := (GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT).2.2.2.2
  have hkf := (GlobalTheory.tensor_decomposition_kfinite hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw).2.1
  have hp : ∀ I (a : ι → ℂ) (w : R.H), R.KFin w → (RI I).KFin (∑ c, pr I c (tm R a w c)) := fun I a w hw =>
    kfin_sum _ fun c => hkf I c _ (kfin_smul (a c) hw)
  exact ⟨fun I => ⟨hp I om v hv, hp I om' v' hv'⟩,
    fun g hg => hadj om om' v (hRT v (hRK v hv)) v' (hRT v' (hRK v' hv')) g hg⟩

end GlobalTheory.KFinCoefSplit
