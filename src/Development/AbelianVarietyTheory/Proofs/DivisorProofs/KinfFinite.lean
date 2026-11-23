module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspKinfFin

theorem kinf_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : GlobalTheory.CuspRep.Kinf E d => fun g : GlobalTheory.CuspRep.GA E d => ψ (ι (g * GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀))) := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι _ _ _ _ _ ψ hψ g₀ hK
  classical
  let T : (GAd σ J → ℂ) →ₗ[ℂ] (GlobalTheory.CuspRep.GA E d → ℂ) :=
    { toFun := fun φ g => φ (ι g * g₀)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hV := hψ.1.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => ψ (g * k))).map T) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨fun x => ψ (x * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)), Submodule.subset_span ⟨⟨_, hK k⟩, rfl⟩, ?_⟩
  funext g
  show ψ (ι g * g₀ * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)) = _
  simp only [map_mul, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CuspKinfFin
