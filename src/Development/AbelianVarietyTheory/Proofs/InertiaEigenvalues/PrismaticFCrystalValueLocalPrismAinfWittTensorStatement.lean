module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensor
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

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism

theorem _root_.GlobalTheory.T.prismaticFCrystal_value_localPrism_ainf_wittTensor : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (PS PW : Obj l ↥(OL K)) (ev : Hom PS PW) (ioH : Hom PS (ainfObj K)) (gH : ↥(GK K) → Hom PS PS) (π Q : PS.A) (ψ : PS.A →+* WCb l), (∀ x, ψ x = inclW l (ainfId K (ioH.f x))) → (∀ g, ioH.comp (gH g) = (ainfHom K g).comp ioH) → (∀ g, ev.comp (gH g) = ev) → RingHom.ker ev.f = Ideal.span {π} → Q ∈ PS.I → IsLocalRing PS.A → ψ Q ≠ 0 → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (E : FCrys l ↥(OL K)) (j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K E (ainfObj K) (ainfId K) T ρ j → ∃ (q : ℕ) (b : Module.Basis (Fin q) PS.A (E.M PS)) (c : Module.Basis (Fin q) (WCb l) (WCb l ⊗[ℤ_[l]] T)), (∀ i, c i = j (E.tr ioH (b i))) ∧ (∀ x, ∃ (k : ℕ) (m : E.M PS), ψ Q ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (E.tr ioH x)) = j (E.tr ioH m)) ∧ (∀ x, ∃ (k : ℕ) (s : Fin q → PS.A), ψ Q ^ k • j (E.tr ioH x) = ∑ i, ψ (s i) • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c i)) ∧ (∀ (g : ↥(GK K)) x, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (j (E.tr ioH x)) = j (E.tr ioH (E.tr (gH g) x))) ∧ (∀ g x, ∃ y, E.tr (gH g) x - x = π • y) := by
  first | exact @GlobalTheory.Prism.LocalValue.main | exact GlobalTheory.Prism.LocalValue.main | (intros; apply GlobalTheory.Prism.LocalValue.main <;> assumption)
