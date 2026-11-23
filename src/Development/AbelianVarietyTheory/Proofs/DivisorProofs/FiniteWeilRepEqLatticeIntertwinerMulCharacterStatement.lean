module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.finiteWeilRep_eq_latticeIntertwiner_mul_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (χS χT : (AE D)ˣ →* Circle) (nS nT : ℕ), IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS nS → ResEta D χT nT → ∀ of : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsFinWeil ψ S T ΛS ΛT χS χT of → ∀ (lam : ℕ →* ℂ), GoodNorm (GlobalTheory.FinWeil.sgO D) lam → (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (w : 𝓞 D.host.E) (Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)), IsLatRep hψ.1 ΛS ΛT w lam Om → ∀ ε, IsHalfIdem D ε → ∀ (g : GA D S) (h : GA D T) (x y : (AE D)ˣ), (x : AE D) = ε * (Formalism.L2.Theta.mt S g).det + (1 - ε) → (y : AE D) = ε * (Formalism.L2.Theta.mt T h).det + (1 - ε) → ∀ f : thetaSub ψ S T, of (g, h) f = ((((χT x)⁻¹ * χS y : Circle) : ℂ)) • (Om (g, h) f : WO S T → ℂ) := by
  first | exact @GlobalTheory.FinWeilForm.finWeil_eq | exact GlobalTheory.FinWeilForm.finWeil_eq | (intros; apply GlobalTheory.FinWeilForm.finWeil_eq <;> assumption)
