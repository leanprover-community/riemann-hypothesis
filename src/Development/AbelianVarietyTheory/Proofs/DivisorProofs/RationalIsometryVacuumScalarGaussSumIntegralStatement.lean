module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsometryVacuumScalarGaussSumIntegral
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalIsometry_vacuumScalar_gaussSum_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 → ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → Function.Bijective (fun x : Matrix (Fin T.rank) (Fin S.rank) D.host.E => b * x * a - x) → Integrable (gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ))) volume → ∀ κ : ℂ, (∀ f : thetaSub ψ S T, Fixes (opF hψ.1 S T w) (latF S T ΛS ΛT) f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ x, (f : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x) = κ * ((sumOp (opF hψ.1 S T w) (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) f : thetaSub ψ S T) : WO S T → ℂ) x) → ∀ (n : ℕ) (t : Fin n → Matrix (Fin T.rank) (Fin S.rank) D.host.E), (∀ k, b * t k * a - t k ∈ latQ S T ΛS ΛT) → (∀ y, b * y * a - y ∈ latQ S T ΛS ΛT → ∃! k, y - t k ∈ latQ S T ΛS ΛT) → ∃ r : ℝ, 0 < r ∧ (∑ k, gamQ ψ S T (GlobalTheory.FinWeil.sgO D w • (b * t k * a - t k)) (t k)) * ∫ v, gaussR S T sS sT (fun τ => a.map (tauE D τ)) (fun τ => b.map (tauE D τ)) v = r * κ := by
  first | exact @GlobalTheory.RatTrace.gauss_mul_integral | exact GlobalTheory.RatTrace.gauss_mul_integral | (intros; apply GlobalTheory.RatTrace.gauss_mul_integral <;> assumption)
